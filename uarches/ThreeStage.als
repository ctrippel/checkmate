module ThreeStage
open checkmate_tutorial

////////////////////////////////////////////////////////////////////////////////////
// Pipeline module
/////////////////////////////////////////////////////////////////////////////////////

// define pipeline locations
one sig Fetch extends Location { }	
one sig Execute extends Location { }
one sig Writeback extends Location { }
one sig StoreBuffer extends Location { }	
one sig L1ViCLCreate extends Location { }	
one sig L1ViCLExpire extends Location { }
one sig MainMemory extends Location { }
one sig Complete extends Location { }

sig mfence extends FenceSC { }

////////////////////////////////////////////////////////////////////////////////////
// Predicates
/////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// processor predicates

// true if Read, r, is sourced from Write, w, via the STB
pred STBFwd[w: Write, r: Read] {
	SameThread[w, r] and
	ProgramOrder[w, r] and
	NoReadViCLs[r] and
	EdgeExists[r, Execute, w, L1ViCLCreate, ustb]
}

// true if all stores before Read, r, have been written to the L1 cache
pred STBEmpty[r: Read] {
	all w : Write |
	SameVirtualAddress[w, r] and
	ProgramOrder[w, r] <=>
	EdgeExists[w, L1ViCLCreate, r, Execute, ustb_flush]
}

// true if Read, r, is sourced from Write, w, via a cache hit in the L1 cache
pred ReadSourcedFromL1[w: Write, r: Read] {
	NoReadViCLs[r] and
	SameCore[w, r] and
	SameVirtualAddress[w, r] and
	not EdgeExists[w, MainMemory, r, L1ViCLCreate, urf] and
	(
		// sourced from Write ViCLs
		(
			EdgeExists[w, L1ViCLCreate, r, Execute, urf] and
			EdgeExists[r, Execute, w, L1ViCLExpire, uvicl]
		)
		or
		// sourced from Read ViCLs
		(
			some r': Read |
			SameCore[r, r'] and
			w->r' in rf and
			NodeExists[r', L1ViCLCreate] and
			EdgeExists[r', L1ViCLCreate, r, Execute, uvicl] and
			EdgeExists[r, Execute, r', L1ViCLExpire, uvicl] and
			EdgeExists[w, L1ViCLExpire, r', L1ViCLCreate, ucci] and
			EdgeExists[w, MainMemory, r', L1ViCLCreate, urf]
		)
	)
}

// true if Read, r, is sourced from a Write, w, via a cache miss in the L1 cache
pred ReadSourcedFromMM[w: Write, r: Read] {
	ReadViCLsExist[r] and
	not EdgeExists[w, L1ViCLCreate, r, Execute, urf] and
	EdgeExists[w, MainMemory, r, L1ViCLCreate, urf] and
	( SameCore[w, r] => EdgeExists[w, L1ViCLExpire, r, L1ViCLCreate, ucci] )
}

// true if Write, w, updates processor memory before Write, w'
pred WriteSerialization[w: Write, w': Write] {
	EdgeExists[w, MainMemory, w', MainMemory, uco] and
	(
		SameCore[w, w'] =>
		EdgeExists[w, L1ViCLCreate, w', L1ViCLCreate, uco] and
		EdgeExists[w, L1ViCLExpire, w', L1ViCLCreate, uco]
	)
}

// true if Read, r, has L1 ViCLs (i.e., if r is a cache miss in the L1 cache)
pred ReadViCLsExist[r: Read] {
   	EdgeExists[r, L1ViCLCreate, r, Execute, uvicl] and
   	EdgeExists[r, Execute, r, L1ViCLExpire, uvicl] and
	NodeExists[r, L1ViCLCreate] and 
	NodeExists[r, L1ViCLExpire]
}

// true if Read, r, does not have L1 ViCLs (i.e., if r is a cache hit in the L1 cache)
pred NoReadViCLs[r: Read] {
	not NodeExists[r, L1ViCLCreate] and 
	not NodeExists[r, L1ViCLExpire]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// OS predicates

// true if there is no shared memory between Attacker and Victim processes
pred NoSharedMem {
	all a : PhysicalAddress |
	( a.region = Victim and a.readers = { Victim } and a.writers = { Victim } ) or
	( a.region = Attacker and a.readers = { Attacker } and a.writers = { Attacker } )
}

// true if there is shared read-only memory between Attacker and Victim processes
// the shared read-only memory lies in the Victim's address space
pred SharedROMem {
	all a : PhysicalAddress | 
	( a.region = Victim and a.readers = { Attacker + Victim } and no a.writers) or
	( a.region = Victim and a.readers = { Victim } and a.writers = { Victim } ) or
	( a.region = Attacker and a.readers = { Attacker } and a.writers = { Attacker } )
}

pred NoInterveningOp[e: Event, e': Event] {
	not (
		some e'': Event |
		ProgramOrder[e, e''] and ProgramOrder[e'', e'] or
		EdgeExists[e, Complete, e'', Fetch, uhb_proc] and EdgeExists[e'', Complete, e', Fetch, uhb_proc]
	)
}
////////////////////////////////////////////////////////////////////////////////////
// Axioms
/////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// processor axioms

// define path for Read ops
fun r_path : Location->Location {
	Fetch->Execute +
	Execute->Writeback +
	Writeback->Complete
}

// define path for Write ops
fun w_path : Location->Location {
	Fetch->Execute +
	Execute->Writeback +
	Writeback->StoreBuffer +
	StoreBuffer->L1ViCLCreate +
	L1ViCLCreate->L1ViCLExpire +
	L1ViCLCreate->MainMemory +
	L1ViCLCreate->Complete
}

// define path for Fence ops
fun f_path : Location->Location {
	Fetch->Execute +
	Execute->Writeback +
	Writeback->Complete
}

// create minimal nodes
// all nodes that *must exist*
fact bound_nodes_min {
	Read->{ Fetch + Execute + Writeback + Complete } +
	Write->{ Fetch + Execute + Writeback + Complete } +
	Fence->{ Fetch + Execute + Writeback + Complete }  in NodeRel
}

// bound nodes so Alloy doesn't create more
// all nodes that *could exist*
fact bound_nodes_max { NodeRel in
	Read->{ Fetch + Execute + Writeback + L1ViCLCreate + L1ViCLExpire + Complete } +
	Write->{  Fetch + Execute + Writeback + StoreBuffer + L1ViCLCreate + L1ViCLExpire + MainMemory + Complete } +
	Fence->{ Fetch + Execute + Writeback + Complete }
}

// all Reads follow r_path
fact Reads_path {
	all r : Read | all disj l, l' : Location |
	l->l' in r_path <=>
	EdgeExists[r, l, r, l', uhb_intra]
}

// all Writes follow w_path
fact Writes_path {
	all w : Write | all disj l, l' : Location |
	l->l' in w_path <=> EdgeExists[w, l, w, l', uhb_intra]
}

// all Fences follow f_path
fact Fences_path {
	all f : Fence | all disj l, l' : Location |
	l->l' in f_path <=>
	EdgeExists[f, l, f, l', uhb_intra]
}

// map rf relations from candidate executions down to uhb edges
fact ReadsFrom {
	all r : Read | all w : Write |
	w->r in rf  <=>
	(
		STBFwd[w, r] or
		(
			STBEmpty[r] and
			(
				ReadSourcedFromL1[w, r] or
				ReadSourcedFromMM[w, r]
			)
		)
	)
}

// map co relations from candidate executions down to uhb edges
fact CoherenceOrder {
	all w : Write | all w' : Write|
	w->w' in co <=>
	WriteSerialization[w, w']
}

// map fr relations from candidate executions down to uhb edges
fact FromReads {
	all r : Read | all w : Write |
	r->w in fr <=>
	(
		SameCore[r, w] and
		EdgeExists[r, Execute, w, Execute, ufr] and
		not EdgeExists[r, L1ViCLCreate, w, MainMemory, ufr]
	) or
	(
		not SameCore[w, r] and
		not EdgeExists[r, Execute, w, Execute, ufr] and
		EdgeExists[r, L1ViCLCreate, w, MainMemory, ufr]
	)
}

// handle cases where reads read from initial state and are thus not part of the rf relation
fact DataFromInitialMM {
	all r : Read | DataFromInitialStateAtPA[r] =>
	(
		STBEmpty[r] and (
			ReadViCLsExist[r] or 
			(	
				NoReadViCLs[r] and
				(some r': Read |
			 	SameCore[r,r'] and
				SameVirtualAddress[r, r'] and
				DataFromInitialStateAtPA[r'] and
				NodeExists[r', L1ViCLCreate] and
				EdgeExists[r', L1ViCLCreate, r, Execute, uvicl] and
				EdgeExists[r, Execute, r', L1ViCLExpire, uvicl] )
			)
		)
	)
}

// mfences drain the store buffer
fact MFENCEOrder { 
	all f: mfence | all w : Write | 
 	SameCore[w, f] and
	(ProgramOrder[w, f] or EdgeExists[w, Complete, f, Fetch, uhb_proc]) <=> 
	EdgeExists[w, MainMemory, f, Execute, ufence]
}

fact Fetch_stage_is_inorder { all disj e, e' : Event 	|
	ProgramOrder[e, e'] <=>
	EdgeExists[e, Fetch, e', Fetch, uhb_inter]
}

fact Execute_state_is_ooo	{ all disj e, e' : Event |
	EdgeExists[e, Fetch, e',  Fetch, uhb_inter] <=>
	EdgeExists[e, Execute, e', Execute, uhb_inter]
}

fact Writeback_stage_is_inorder { all disj e, e' : Event |
	EdgeExists[e, Execute, e', Execute, uhb_inter] <=>
	EdgeExists[e, Writeback, e', Writeback, uhb_inter]
}

fact STB_FIFO { all disj w, w' : Write |
	EdgeExists[w, Writeback, w', Writeback, uhb_inter] <=>
	EdgeExists[w, StoreBuffer, w', StoreBuffer, uhb_inter]
}

fact STB_OneAtATime { all disj w, w' : Write |
	EdgeExists[w, StoreBuffer, w', StoreBuffer, uhb_inter] <=>
	(
		EdgeExists[w, L1ViCLCreate, w', StoreBuffer, uhb_inter] and
		not EdgeExists[w, MainMemory, w', StoreBuffer, uhb_inter]
	)
}	

fact Complete_stage_is_inorder { all disj e, e' : Event |
	EdgeExists[e, Fetch, e', Fetch, uhb_inter] <=>
	EdgeExists[e, Complete, e', Complete, uhb_inter]
} 	

// single writer, multiple reader invariant
fact SWMR {	
	all w: Write | all e: MemoryEvent |
	(
		not SameEvent[w, e] and 
		SamePhysicalAddress[w, e] and
		NodeExists[e, L1ViCLCreate] and 
		NodeExists[w, L1ViCLCreate]
	) =>
	(
		EdgeExists[e, L1ViCLExpire, w, L1ViCLCreate, ucci] or
		EdgeExists[w, L1ViCLCreate, e, L1ViCLCreate, ucci]
	)
}

fact L1ViCLNoDups {
	all e: MemoryEvent | all e' : MemoryEvent |
	(
		not SameEvent[e, e'] and
		SameCore[e, e'] and
		NodeExists[e, L1ViCLCreate] and
		NodeExists[e', L1ViCLCreate] and
		(
			SameIndexL1[e, e'] or
			SamePhysicalAddress[e, e']
		) 
	) =>
	(
		EdgeExists[e, L1ViCLExpire, e', L1ViCLCreate, ucci] and EdgeExists[e, L1ViCLCreate, e', L1ViCLCreate, ucci] or
		EdgeExists[e', L1ViCLExpire, e, L1ViCLCreate, ucci] and EdgeExists[e', L1ViCLExpire, e, L1ViCLCreate, ucci]
	) 
}

fact NoSpeculation {
	all e : MemoryEvent |
	not IsIllegalRead[e] and
	not IsIllegalWrite[e]
}

fact L1ViCLPairs {
	all e: Event |
	NodeExists[e, L1ViCLCreate] <=>
	NodeExists[e, L1ViCLExpire]
}

fact OneViCLSource {
	all e, e' : MemoryEvent |
	(
		EdgeExists[e, L1ViCLCreate, e', Execute, uvicl] =>
		(no e'': Event | not SameEvent[e, e''] and EdgeExists[e'', L1ViCLCreate, e', Execute, uvicl])
	) and 
	(
		EdgeExists[e', Execute, e, L1ViCLExpire, uvicl] =>
		(no e'': MemoryEvent | not SameEvent[e, e''] and EdgeExists[e', Execute, e'', L1ViCLExpire, uvicl])
	)
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// OS axioms

fact AssignThd {
	all disj e, e': Event |
	SameThread[e, e'] =>
	(
		SameProcess[e, e'] and
		SameCore[e, e']
	)
}	

fact ThdAffinity {
	all disj e, e' : Event |
	SameProcess[e, e'] and
	not SameThread[e, e'] =>
	not SameCore[e, e']
} 

fact SharedResources {
	all a : AttackerEvent | all v: VictimEvent |
	SameCore[a, v] =>
	(
		EdgeExists[a, Complete, v, Fetch, uhb_proc] or
		EdgeExists[v, Complete, a, Fetch, uhb_proc]
	)
}
// no pre-fetching across process boundaries
fact Prefetching {
	all e, e': Event |
	EdgeExists[e, Complete, e', Fetch, uhb_proc] =>
	(
		NodeExists[e', L1ViCLCreate] =>
		EdgeExists[e, Complete, e', L1ViCLCreate, uhb_proc]
	) and 
	(
		all e'': Event |
		ProgramOrder[e', e''] and
		NodeExists[e'', L1ViCLCreate] =>
		EdgeExists[e, Complete, e'', L1ViCLCreate, uhb_proc]
	)
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// bound relations (Alloy-specific)

fact bound_uhb_inter { uhb_inter in
	Event->Fetch->Event->Fetch + 
	Event->Execute->Event->Execute +
	Event->Writeback->Event->Writeback +
	Write->StoreBuffer->Write->StoreBuffer +
	Write->L1ViCLCreate->Write->StoreBuffer +
	Write->MainMemory->Write->StoreBuffer +
	Event->Complete->Event->Complete
}

fact bound_urf { urf in 
	Write->L1ViCLCreate->Read->Execute +
	Write->MainMemory->Read->L1ViCLCreate
}

fact bound_uco { uco in
	Write->L1ViCLCreate->Write->L1ViCLCreate +
	Write->L1ViCLExpire->Write->L1ViCLCreate +
	Write->MainMemory->Write->MainMemory
}

fact bound_ufr { ufr in
	Read->Execute->Write->Execute +
	Read->L1ViCLCreate->Write->MainMemory 
}

fact bound_ustb_flush { ustb_flush in
	Write->L1ViCLCreate->Read->Execute
}

fact bound_ustb { ustb in
	Read->Execute->Write->L1ViCLCreate
}

fact bound_ufence { ufence in
	Write->MainMemory->Fence->Execute
}

fact bound_uvicl { uvicl in
	Read->L1ViCLCreate->Read->Execute + 
	Read->Execute->Read->L1ViCLExpire + 
	Read->Execute->Write->L1ViCLExpire
}  

fact bound_ucci { ucci in
	Event->L1ViCLCreate->Event->L1ViCLCreate + 
	Event->L1ViCLExpire->Event->L1ViCLCreate
}

fact bound_uhb_proc { uhb_proc in 
	AttackerEvent->Complete->VictimEvent->Fetch + 
	VictimEvent->Complete->AttackerEvent->Fetch +
	AttackerEvent->Complete->VictimEvent->L1ViCLCreate +
	VictimEvent->Complete->AttackerEvent->L1ViCLCreate
}

fact urf_implies_rf { 
	all w : Write | all r : Read | 	all l, l' : Location |
	EdgeExists[w, l, r, l', urf] => w->r in rf
}

fact uco_implies_co {
	all disj w, w' : Write | all l, l' : Location | 
	EdgeExists[w, l, w', l', uco] => w->w' in co
}

fact ufr_implies_fr {
	all r : Read | all w : Write | all l, l' : Location |
	EdgeExists[r, l, w, l', ufr] => r->w in fr
}

fact ustb_implies_rf {
	all r : Read, w : Write | 	all l, l' : Location |
	EdgeExists[r, l, w, l', ustb] => w->r in rf and STBFwd[w, r]  
}

fact assign_uhb_to_procs {
	all e, e' : Event | all l, l' : Location |
	(
		EdgeExists[e, l, e', l', ustb]  or
		EdgeExists[e, l, e', l', ustb_flush] or
		EdgeExists[e, l, e', l', uhb_inter]  or
		EdgeExists[e, l, e', l', uhb_intra] 
	) => SameProcess[e, e']
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Threat Descriptions= 

// to reduce false positives, cachelines won't be spuriously evicted
fact ExplicitEvictions {
	all disj e, e' : Event |
	IsAnyRead[e'] and
	NodeExists[e, L1ViCLCreate] and
	(IsAnyRead[e] and SameSourcingWrite[e, e'] or IsAnyWrite[e] and (e->e' in rf)) and
	(ProgramOrder[e, e'] or EdgeExists[e, Complete, e', Fetch, uhb_proc]) and
	(no e'' : Event | not SameEvent[e'', e'] and EdgeExists[e, L1ViCLExpire, e'', L1ViCLCreate])
	=> EdgeExists[e, L1ViCLCreate, e', Execute] and EdgeExists[e', Execute, e, L1ViCLExpire]
}

pred flush_reload {
	some disj a, a', f : AttackerEvent |
	ProgramOrder[a, f] and
	ProgramOrder[f, a'] and
	IsAnyMemory[a] and
	IsAnyRead[a'] and
	NodeExists[a, L1ViCLCreate] and
	not NodeExists[a', L1ViCLCreate] and 
	CanSourceL1[a, a'] and	
	EdgeExists[a, L1ViCLExpire, f, Execute] and

	// access before the flush is useful for pedagogy
	// therefore, don't interleave ops between access a and f
	NoInterveningOp[a, f] and

	// attacker will not avoid its own exploit
	not (some e: AttackerEvent |
  		ProgramOrder[f, e] and 
		ProgramOrder[e, a'] and 
		SameVirtualAddress[e, a'] and
		IsAnyMemory[e]) and

	// exploit starts at the access before the flush phase and ends after the reload phase
  	not (some e: AttackerEvent | ProgramOrder[e, a]) and
  	not (some e: AttackerEvent | ProgramOrder[a', e]) and
  	not (some e: Event | EdgeExists[e, Complete, a, Fetch, uhb_proc]) and
  	not (some e: Event | EdgeExists[a', Complete, e, Fetch, uhb_proc])
}

pred prime_probe {
	some disj a, a' : AttackerEvent |
	ProgramOrder[a, a'] and
	IsAnyMemory[a] and	
	IsAnyRead[a'] and	
	NodeExists[a, L1ViCLCreate] and 
	NodeExists[a', L1ViCLCreate] and 
        CanSourceL1[a, a'] and
	
	// attacker will not avoid its own exploit
	not (some e: AttackerEvent |
		ProgramOrder[a, e] and 
		ProgramOrder[e, a'] and 
		SameIndexL1[e, a] and
		IsAnyMemory[e]) and

	// exploit starts at the prime phase and ends after the probe phase
  	not (some e: AttackerEvent | ProgramOrder[e, a]) and
  	not (some e: AttackerEvent | ProgramOrder[a', e]) and
  	not (some e: Event | EdgeExists[e, Complete, a, Fetch, uhb_proc]) and
  	not (some e: Event | EdgeExists[a', Complete, e, Fetch, uhb_proc])
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Tests= 

run test_flush_reload {
	SharedROMem and
	flush_reload and 
	NumProcessThreads[1, Attacker] and
	NumProcessThreads[1, Victim] and
	ucheck
} for 32 but 1 Core, 2 Process, 1 CacheIndexL1, 4 Address, 2 PhysicalAddress, 2 VirtualAddress, 8 Location, 4 Event

run test_prime_probe {
	NoSharedMem and
	prime_probe and 
	NumProcessThreads[1, Attacker] and
	NumProcessThreads[1, Victim] and
	ucheck
} for 24 but 1 Core, 2 Process, 1 CacheIndexL1, 4 Address, 2 PhysicalAddress, 2 VirtualAddress, 8 Location, 3 Event
