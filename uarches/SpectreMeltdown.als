module SpectreMeltdown
open checkmate

fact { no coh }
fact { no ucoh_inter }
fact { no ucoh_intra }

////////////////////////////////////////////////////////////////////////////////////
// Pipeline module
/////////////////////////////////////////////////////////////////////////////////////

// define pipeline locations
one sig Fetch extends Location { }	
one sig Execute extends Location { }
one sig ReorderBuffer extends Location { }	
one sig PermissionCheck extends Location { }
one sig Commit extends Location { }
one sig StoreBuffer extends Location { }	
one sig ViCLCreate extends Location { }	
one sig ViCLExpire extends Location { }
one sig MainMemory extends Location { }
one sig Complete extends Location { }

// instruction paths
fun SquashedEvent : Event { Event - NodeRel.Commit }
fun CommittedEvent : Event { NodeRel.Commit }

fact 	{ all b : Branch <: SquashedEvent | all disj l, l' : Location | l->l' in br_path_squash <=> EdgeExists[b, l, b, l', uhb_intra] }
fact 	{ all b : Branch <: CommittedEvent | all disj l, l' : Location | l->l' in br_path_commit <=> EdgeExists[b, l, b, l', uhb_intra] }

fact 	{ all c : CacheFlush <: SquashedEvent | all disj l, l' : Location | l->l' in cf_path_squash <=> EdgeExists[c, l, c, l', uhb_intra] }
fact 	{ all c : CacheFlush <: CommittedEvent | all disj l, l' : Location | l->l' in cf_path_commit <=> EdgeExists[c, l, c, l', uhb_intra] }

fact 	{ all r : Read <: SquashedEvent	| all disj l, l' : Location | l->l' in r_path_squash <=> EdgeExists[r, l, r, l', uhb_intra] }
fact 	{ all r : Read <: CommittedEvent | all disj l, l' : Location | l->l' in r_path_commit <=> EdgeExists[r, l, r, l', uhb_intra] }

fact 	{ all w : CacheableWrite	<: SquashedEvent | all disj l, l' : Location | l->l' in wc_path_squash <=> EdgeExists[w, l, w, l', uhb_intra] }
fact 	{ all w : CacheableWrite	<: CommittedEvent | all disj l, l' : Location | l->l' in wc_path_commit <=> EdgeExists[w, l, w, l', uhb_intra] }
fact 	{ all w : NonCacheableWrite	<: SquashedEvent | all disj l, l' : Location | l->l' in wnc_path_squash <=> EdgeExists[w, l, w, l', uhb_intra] }
fact 	{ all w : NonCacheableWrite	<: CommittedEvent | all disj l, l' : Location | l->l' in wnc_path_commit <=> EdgeExists[w, l, w, l', uhb_intra] }

// create minimal nodes
// all nodes that *must exist* 
fact {
	Branch->{ Fetch + Execute + ReorderBuffer + PermissionCheck + Complete } +
 	CacheFlush->{ Fetch + Execute + ReorderBuffer + PermissionCheck + Complete } +
	CacheableRead->{ Fetch + Execute + ReorderBuffer + PermissionCheck + Complete } +				
   	NonCacheableRead->{ Fetch + Execute + ReorderBuffer + PermissionCheck + Complete } +
   	CacheableWrite->{  Fetch + Execute + ReorderBuffer + PermissionCheck + Complete } +
	NonCacheableWrite->{  Fetch + Execute + ReorderBuffer + PermissionCheck + Complete }  in NodeRel
}	

// bound nodes so Alloy doesn't create more
// all nodes that *could exist*
fact { NodeRel in 
	Branch->{ Fetch + Execute + ReorderBuffer + PermissionCheck + Commit + Complete } +
	CacheFlush->{ Fetch + Execute + ReorderBuffer + PermissionCheck + Commit + Complete } +
	CacheableRead->{  Fetch + Execute + ReorderBuffer + PermissionCheck + Commit + ViCLCreate + ViCLExpire + Complete } +
   	NonCacheableRead->{  Fetch + Execute + ReorderBuffer + PermissionCheck + Commit + Complete } +				
	CacheableWrite->{  Fetch + Execute + ReorderBuffer + PermissionCheck + Commit + StoreBuffer + ViCLCreate + ViCLExpire + MainMemory + Complete } +													
	NonCacheableWrite->{  Fetch + Execute + ReorderBuffer + PermissionCheck + Commit + StoreBuffer + MainMemory + Complete } 
}

// define branch squash path (no commit node)
fun br_path_squash : Location->Location {
	Fetch->Execute +
	Execute->ReorderBuffer +
	ReorderBuffer->PermissionCheck +
	PermissionCheck->Complete
}	

// define branch commit path
fun br_path_commit : Location->Location {
	Fetch->Execute +
	Execute->ReorderBuffer +
	ReorderBuffer->PermissionCheck +
	PermissionCheck->Commit +
    Commit->Complete
}	

// define branch squash path (no commit node)
fun cf_path_squash : Location->Location {
	Fetch->Execute +
	Execute->ReorderBuffer +
	ReorderBuffer->PermissionCheck +
	PermissionCheck->Complete
}	

// define cflush commit path
fun cf_path_commit : Location->Location {
	Fetch->Execute +
	Execute->ReorderBuffer +
	ReorderBuffer->PermissionCheck +
	PermissionCheck->Commit +
    Commit->Complete
}	

// define fence squash path (no commit node)
fun f_path_squash : Location->Location {
 	Fetch->Execute +
	Execute->ReorderBuffer +
	ReorderBuffer->Complete
}	

// define fence commit path
fun f_path_commit: Location->Location {
 	Fetch->Execute +
	Execute->ReorderBuffer +
	ReorderBuffer->Commit +
    Commit->Complete
}

// define read squash path (no commit node)
fun r_path_squash : Location->Location {
 	Fetch->Execute +
	Execute->ReorderBuffer +
    ReorderBuffer->PermissionCheck +
	PermissionCheck->Complete
}	

// define read commit path
fun r_path_commit : Location->Location {
 	Fetch->Execute +
	Execute->ReorderBuffer +
    ReorderBuffer->PermissionCheck +
	PermissionCheck->Commit +
    Commit->Complete
}	

// define cacheable write squash path (no commit node)
fun wc_path_squash : Location->Location { 
	Fetch->Execute +
	Execute->ReorderBuffer +
    ReorderBuffer->PermissionCheck +
	PermissionCheck->Complete
}

// define cacheable write commit path
fun wc_path_commit : Location->Location { 
	Fetch->Execute +
	Execute->ReorderBuffer +
    ReorderBuffer->PermissionCheck +
	PermissionCheck->Commit +
	Commit->StoreBuffer +
	StoreBuffer->ViCLCreate +
	ViCLCreate->ViCLExpire +
	ViCLCreate->MainMemory +
    ViCLCreate->Complete
} 	

// define non-cacheable write squash path (no commit node)
fun wnc_path_squash : Location->Location { 
	Fetch->Execute +
	Execute->ReorderBuffer +
    ReorderBuffer->PermissionCheck +
	PermissionCheck->Complete
}

// define non-cacheable write commit path
fun wnc_path_commit : Location->Location { 
	Fetch->Execute +
	Execute->ReorderBuffer +
    ReorderBuffer->PermissionCheck +
	PermissionCheck->Commit +
	Commit->StoreBuffer +
	StoreBuffer->MainMemory +
    MainMemory->Complete
} 	

// uhb_inter: inter-instruction happens-before
fact Fetch_stage_is_inorder { all disj e, e' : Event 	|
	ProgramOrder[e, e'] <=>
	EdgeExists[e, Fetch, e', Fetch, uhb_inter]
}

fact Execute_state_is_ooo	{ all disj e, e' : Event |
	(EdgeExists[e, Fetch, e',  Fetch, uhb_inter] and (SamePhysicalAddress[e, e'] or HasDependency[e, e'] or IsAnyFence[e] or IsAnyFence[e'])) <=>
	EdgeExists[e, Execute, e', Execute, uhb_inter]
}

fact Commit_stage_is_inorder { all disj e, e' : Event |
	(EdgeExists[e, Fetch, e', Fetch, uhb_inter] and NodeExists[e, Commit] and NodeExists[e', Commit]) <=>
	EdgeExists[e, Commit, e', Commit, uhb_inter]
}

fact STB_FIFO { all disj w, w' : Write |
	EdgeExists[w, Commit, w', Commit, uhb_inter] <=>
	EdgeExists[w, StoreBuffer, w', StoreBuffer, uhb_inter]
}

fact STB_OneAtATime { all disj w, w' : Write |
	EdgeExists[w, StoreBuffer, w', StoreBuffer, uhb_inter] <=>
	((IsCacheable[w] and EdgeExists[w, ViCLCreate, w', StoreBuffer, uhb_inter] and not EdgeExists[w, MainMemory, w', StoreBuffer, uhb_inter]) or
	(not IsCacheable[w] and EdgeExists[w, MainMemory, w', StoreBuffer, uhb_inter]))
}	

fact Complete_stage_is_inorder { all disj e, e' : Event |
	EdgeExists[e, Fetch, e', Fetch, uhb_inter] <=>
	EdgeExists[e, Complete, e', Complete, uhb_inter]
} 	

fact bound_uhb_inter { uhb_inter in
	Event->Fetch->Event->Fetch + 
	Event->Execute->Event->Execute +
	Event->Commit->Event->Commit +
	Write->StoreBuffer->Write->StoreBuffer +
	Write->ViCLCreate->Write->StoreBuffer +
	Write->MainMemory->Write->StoreBuffer +
	Event->Complete->Event->Complete
}

////////////////////////////////////////////////////////////////////////////////////
// Predicates
/////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////
// Communication predicates
pred ReadViCLsExist[r: Read] {
    EdgeExists[r, ViCLCreate, r, Execute, uvicl] and
    EdgeExists[r, Execute, r, ViCLExpire, uvicl] and
	NodeExists[r, ViCLCreate] and 
	NodeExists[r, ViCLExpire]
}

pred NoReadViCLs[r: Read] {
	not NodeExists[r, ViCLCreate] and 
	not NodeExists[r, ViCLExpire]
}

// true if read is sourced from STB
// i.e., if it executes before the write reaches the L1 Cache
pred STBFwd[w: Write, r: Read] {
	SameThread[w, r] and
	ProgramOrder[w, r] and
	NoReadViCLs[r] and
	EdgeExists[w, Execute, r, Execute, urf] and
	(
		NodeExists[w, Commit] and IsCacheable[w] and EdgeExists[r, Execute, w, ViCLCreate, ustb] or	
		NodeExists[w, Commit] and not IsCacheable[w] and EdgeExists[r, Execute, w, MainMemory, ustb] or
		not NodeExists[w, Commit] and EdgeExists[r, Execute, w, PermissionCheck, ustb]
	)
}

// true if all stores before read have been written to the L1 Cache (Cacheable) or Main Memory (NonCacheable)
pred STBEmpty[r: Read] {
	all w : Write | SameVirtualAddress[w, r] and ProgramOrder[w, r] and NodeExists[w, Commit] <=>
	(
		(
			IsCacheable[w] and EdgeExists[w, ViCLCreate, r, Execute, ustb_flush] or 
			not IsCacheable[w] and EdgeExists[w, MainMemory, r, Execute, ustb_flush]
		)
	)
}

// true if read is source from the L1 (i.e., from another access' ViCLs
// can read from a write's ViCL or can read from a read's ViCL
pred ReadSourcedFromL1[w: Write, r: Read] {
	SameCore[w, r] and
	NoReadViCLs[r] and
	IsCacheable[r] and
 	SameVirtualAddress[w, r] and
	NodeExists[w, Commit] and
	(
		(
			IsCacheable[w] and
			EdgeExists[w, ViCLCreate, r, Execute, urf] and
			EdgeExists[r, Execute, w, ViCLExpire, uvicl]
		)	
		or 
		(
			some r': Read |
			SameCore[r, r'] and
			w->r' in rf and
			NodeExists[r', ViCLCreate] and
			EdgeExists[r', ViCLCreate, r, Execute, uvicl] and
			EdgeExists[r, Execute, r', ViCLExpire, uvicl] and 
			(
				IsCacheable[w] and EdgeExists[w, ViCLExpire, r', ViCLCreate, ucci] and EdgeExists[w, MainMemory, r', ViCLCreate, urf] or
				not IsCacheable[w] and EdgeExists[w, MainMemory, r', ViCLCreate, urf]
			)
		)
	)
}

// true if read is sourced from a same-core write from Main Memory
pred InternalReadSourcedFromMM[w: Write, r: Read] {
	SameCore[w, r] and
	NodeExists[w, Commit] and
	(
		(
			IsCacheable[r] and
			ReadViCLsExist[r] and
			EdgeExists[w, MainMemory, r, ViCLCreate, urf] and
			(
				IsCacheable[w] and EdgeExists[w, ViCLExpire, r, ViCLCreate, ucci] or
				not IsCacheable[w]
			)
		)
		or
		(
			not IsCacheable[r] and EdgeExists[w, MainMemory, r, Execute, urf] 
		)
	)
}

// true if read is rouced from a different-core write from Main Memory
pred ExternalReadSourcedFromMM[w: Write, r: Read] {
	not SameCore[w, r] and NodeExists[w, Commit] and
	(
		(
			IsCacheable[r] and
			ReadViCLsExist[r] and
			EdgeExists[w, MainMemory, r, ViCLCreate, urf]
		)
		or
		(	
			not IsCacheable[r] and
			EdgeExists[w, MainMemory, r, Execute, urf]
		)
	)
}

pred SameCoreCoherence[w: Write, w': Write] {
	SameCore[w, w'] and NodeExists[w, Commit] and NodeExists[w', Commit] and 
	(
		(
			(IsCacheable[w] and IsCacheable[w']) and
			EdgeExists[w, ViCLCreate, w', ViCLCreate, uco] and
			EdgeExists[w, ViCLExpire, w', ViCLCreate, uco] and
    		EdgeExists[w, MainMemory, w', MainMemory, uco]
		)
		or
		(
			not (IsCacheable[w] and IsCacheable[w']) and
			EdgeExists[w, MainMemory, w', MainMemory, uco]
		)
	)
}

pred DifferentCoreCoherence[w: Write, w': Write] {
	not SameCore[w, w'] and NodeExists[w, Commit] and NodeExists[w', Commit] and 
    EdgeExists[w, MainMemory, w', MainMemory, uco]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// shared memory predicates
pred no_shared_mem { all a : PhysicalAddress |	(Attacker in a.region => (a.readers = { Attacker } and a.writers = { Attacker })) and
																			(Victim in a.region => (a.readers = { Victim } and a.writers = { Victim }))
}

pred shared_ro_mem { all a : PhysicalAddress | (Victim in a.region => a.readers = { Attacker + Victim } and no a.writers) }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// speculation predicates
// two instructions can execute in the window of a mispredicted branch; can be increased if desired
pred SpecWindowOne[e : Event] { some b : MispredictedBranch | b->e in po }
pred SpecWindowTwo[e' : Event] { some e : Event | not SameEvent[e, e'] and e->e' in po and (some b : MispredictedBranch | b->e in po) }

////////////////////////////////////////////////////////////////////////////////////
// Axioms
/////////////////////////////////////////////////////////////////////////////////////

fact NonCacheableReadViCLs { all r: NonCacheableRead | NoReadViCLs[r] }
fact ViCLPairs { all e: Event | NodeExists[e, ViCLCreate] <=> NodeExists[e, ViCLExpire] }

// disallow trailing flushes and fences
fact no_trailing_flush { all c : CacheFlush | c in Event.po and c in po.Event }
fact no_trailing_fence { all f : Fence | f in Event.po and f in po.Event }

fact FenceSC_order { 
	all f: Fence | all w : Write | 
 	SameCore[w, f] and
	(ProgramOrder[w, f] or EdgeExists[w, Complete, f, Fetch, uhb_proc]) <=> 
    EdgeExists[w, MainMemory, f, Execute, ufence]
}

fact one_flush_edge { 
	all w : Write | all r : Read |
	not (EdgeExists[w, ViCLCreate, r, Execute, ustb_flush] and EdgeExists[w, MainMemory, r, Execute, ustb_flush])
}

fact flush_implies_squash { 
	all w: Write | all r : Read |
	(EdgeExists[w, ViCLCreate, r, Execute, ustb_flush] => IsCacheable[w] and NodeExists[w, Commit]) and
	(EdgeExists[w, MainMemory, r, Execute, ustb_flush] => not IsCacheable[w] and NodeExists[w, Commit])
}

fact ReadsFrom {
	all r : Read | all w : Write | w->r in rf  =>
	(
		STBFwd[w, r] or												
		STBEmpty[r] and (	
			ReadSourcedFromL1[w, r] or									
			InternalReadSourcedFromMM[w, r] or
			ExternalReadSourcedFromMM[w, r]
		)
	)
}

fact constrain_urf { 
	all w : Write | all r : Read |
	not (EdgeExists[w, MainMemory, r, ViCLCreate, urf] and EdgeExists[w, MainMemory, r, Execute, urf]) and
	not (EdgeExists[w, MainMemory, r, ViCLCreate, urf] and EdgeExists[w, ViCLCreate, r, Execute, urf]) and
	not (EdgeExists[w, MainMemory, r, ViCLCreate, urf] and EdgeExists[w, Execute, r, Execute, urf]) and
	not (EdgeExists[w, ViCLCreate, r, Execute, urf] and EdgeExists[w, MainMemory, r, Execute, urf]) and
	not (EdgeExists[w, ViCLCreate, r, Execute, urf] and EdgeExists[w, Execute, r, Execute, urf]) and
	not (EdgeExists[w, Execute, r, Execute, urf] and EdgeExists[w, MainMemory, r, Execute, urf]) and
	not (EdgeExists[w, Execute, r, Execute, urf] and EdgeExists[w, ViCLCreate, r, Execute, ustb_flush])
}

fact CoherenceOrder {
	all w : Write | all w' : Write| w->w' in co =>
	(
		SameCoreCoherence[w, w'] or
		DifferentCoreCoherence[w, w'] or
		(not (NodeExists[w, Commit] and NodeExists[w', Commit]))
	)
}

fact FromReads {
 	all r : Read | all w : Write | r->w in fr =>
	(
		SameCore[r, w] and
		EdgeExists[r, Execute, w, Execute, ufr]
	) or
	(
		not SameCore[w, r] and not EdgeExists[r, Execute, w, Execute, ufr] and
		(
			( 	IsCacheable[r] and NodeExists[w, Commit] and EdgeExists[r, ViCLCreate, w, MainMemory, ufr] ) or
			(  not IsCacheable[r] and NodeExists[w, Commit] and EdgeExists[r, Execute, w, MainMemory, ufr] ) or
			(  not NodeExists[w, Commit] )
		)
	)
}

fact CFLUSH_order { 
	all c : CacheFlush | all e : CacheableEvent |
	(
		SameVirtualAddress[e, c] and
 		SameCore[e, c] and
		NodeExists[e, ViCLCreate] and
  		(
			(SameProcess[e, c] and ProgramOrder[e, c]) or
			(not SameProcess[e, c] and EdgeExists[e, Complete, c, Fetch, uhb_proc]) 
    	)
	)
   <=>
	EdgeExists[e, ViCLExpire, c, Execute, uflush]
} 

fact DataFromInitialMM {
    all r : Read | DataFromInitialStateAtPA[r] and IsCacheable[r] =>
    (
		STBEmpty[r] and (
			ReadViCLsExist[r] or 
	    	(	
				NoReadViCLs[r] and
				(some r': Read |
			 	SameCore[r,r'] and
				SameVirtualAddress[r, r'] and
				DataFromInitialStateAtPA[r'] and
				NodeExists[r', ViCLCreate] and
				EdgeExists[r', ViCLCreate, r, Execute, uvicl] and
				EdgeExists[r, Execute, r', ViCLExpire, uvicl] )
			)
		)
	)
}

fact diff_reads_sourced_initial_l1 {
	all disj r, r' : Read | 
	EdgeExists[r, ViCLCreate, r', Execute, uvicl] and
	EdgeExists[r', Execute, r, ViCLExpire, uvicl] =>
	(SameVirtualAddress[r, r'] and 
	(
		(DataFromInitialStateAtPA[r] and DataFromInitialStateAtPA[r']) or
		(
			some w : Write | 	w->r in rf and
										w->r' in rf and
                                		NodeExists[w, Commit] and
										NodeExists[r, ViCLCreate] and
										not NodeExists[r', ViCLCreate] and
										ReadSourcedFromL1[w, r']
		)
	))
}

fact read_miss_vicls { 
  	all r : Read |
  	EdgeExists[r, ViCLCreate, r, Execute, uvicl] and
   	EdgeExists[r, Execute, r, ViCLExpire, uvicl] =>
  	(
		DataFromInitialStateAtPA[r] or
		(some w : Write | w->r in rf and (InternalReadSourcedFromMM[w, r] or ExternalReadSourcedFromMM[w, r]))
	)
}

fact SWMR {	
    all w: Write | all e: MemoryEvent |
		(not SameEvent[w, e] and 
		SamePhysicalAddress[w, e] and
		NodeExists[e, ViCLCreate] and 
		NodeExists[w, ViCLCreate]) =>
		(EdgeExists[e, ViCLExpire, w, ViCLCreate, ucci] or EdgeExists[w, ViCLCreate, e, ViCLCreate, ucci])
}

fact SWMRidx {	
	all e: MemoryEvent | all e' : MemoryEvent |
		(
			not SameEvent[e, e'] and
			SameCore[e, e'] and
			SameIndexL1[e, e'] and
			NodeExists[e, ViCLCreate] and
			NodeExists[e', ViCLCreate]
		) => (EdgeExists[e, ViCLCreate, e', ViCLCreate, ucci] or EdgeExists[e', ViCLCreate, e, ViCLCreate, ucci]) 
}

fact L1ViCLNoDups {
        all e: MemoryEvent | all e' : MemoryEvent |
		(
			not SameEvent[e, e'] and
			SameCore[e, e'] and
			(SameIndexL1[e, e'] or SamePhysicalAddress[e, e']) and
			NodeExists[e, ViCLCreate] and
			NodeExists[e', ViCLCreate]
		) => (EdgeExists[e, ViCLExpire, e', ViCLCreate, ucci] or EdgeExists[e', ViCLExpire, e, ViCLCreate, ucci]) 
}

fact same_core_read_vicls { all disj r, r' : Read | EdgeExists[r, ViCLExpire, r', ViCLCreate, ucci] => SameCore[r, r'] }

fact swmr_or_conflict {
  all e, e' : MemoryEvent |
  (
	EdgeExists[e, ViCLCreate, e', ViCLCreate, ucci] 
	=> (IsAnyWrite[e] or (SameCore[e, e'] and SameIndexL1[e, e']))
  )
}

fact swmr_nodups_or_conflict {
  all e, e' : MemoryEvent |
  (
	EdgeExists[e, ViCLExpire, e', ViCLCreate, ucci] 
	=> SamePhysicalAddress[e, e'] or (SameCore[e, e'] and SameIndexL1[e, e'])
  )
}

fact SingleReadSource { 
	all r: Read | 
		not ( some r' : Read | some w : Write | EdgeExists[r', ViCLCreate, r, Execute, uvicl] and EdgeExists[w, ViCLCreate, r, Execute, urf]) and
		not ( some r' : Read | some w : Write | EdgeExists[r', ViCLCreate, r, Execute, uvicl] and EdgeExists[w, MainMemory, r, Execute, urf])
}

fact constrain_vicls_involving_writes {
	all r : Read | all w : Write |
	EdgeExists[r, Execute, w, ViCLExpire, uvicl] =>
	w->r in rf and EdgeExists[w, ViCLCreate, r, Execute, urf] and ReadSourcedFromL1[w, r]
}

fact constrain_uvicl_source {
	all r: Read | all e: MemoryEvent |
	(EdgeExists[r, ViCLCreate, e, Execute, uvicl] => (no r': Read | not SameEvent[r, r'] and EdgeExists[r', ViCLCreate, e, Execute, uvicl]))
}

fact constrain_uvicl_execute {
	all e, e' : MemoryEvent |
	(EdgeExists[e', Execute, e, ViCLExpire, uvicl] => (no e'': MemoryEvent | not SameEvent[e, e''] and EdgeExists[e', Execute, e'', ViCLExpire, uvicl]))
}

fact map_dep_to_udep {
	all disj e, e': Event | HasDependency[e, e'] <=> EdgeExists[e, Execute, e', Execute, udep]
}

fact dep_vicl_source {
	all disj e, e': Event | (HasDependency[e, e'] and NodeExists[e, ViCLCreate] and NodeExists[e', ViCLCreate] ) <=> EdgeExists[e, ViCLCreate, e', ViCLCreate, udep]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// threading and process scheduling
fact assign_thds_to_procs { all disj e, e': Event | SameThread[e, e'] => SameProcess[e, e'] }	
fact assign_thds_to_cores { all disj e, e' : Event | SameThread[e, e'] => SameCore[e, e'] }
fact same_proc_diff_thds_diff_cores { all disj e, e' : Event | SameProcess[e, e'] and not SameThread[e, e'] => not SameCore[e, e'] } 
fact time_mux_attacker_vicitim { all a : AttackerEvent | all v: VictimEvent | SameCore[a, v] => (EdgeExists[a, Complete, v, Fetch, uhb_proc] or EdgeExists[v, Complete, a, Fetch, uhb_proc]) }

fact assign_uhb_to_procs {
    all e, e' : Event | all l, l' : Location |
    (
		EdgeExists[e, l, e', l', ustb]  or
		EdgeExists[e, l, e', l',	ustb_flush] or
		EdgeExists[e, l, e', l', udep]  or
		EdgeExists[e, l, e', l', uhb_spec]  or
		EdgeExists[e, l, e', l', uhb_inter]  or
		EdgeExists[e, l, e', l', uhb_intra] 
	) => SameProcess[e, e']
}

// memory access permissions
fact no_shared_attacker_memory { all a : PhysicalAddress | Attacker in a.region => ( a.readers = { Attacker } and a.writers = { Attacker } ) }
fact no_shared_or_ro_victim_memory { all a : PhysicalAddress | Victim in a.region => ( a.readers = { Attacker + Victim } and no a.writers) or ( a.readers = { Victim } and a.writers = { Victim } ) }

// no pre-fetching across process boundaries
fact no_prefetch_samecore_diffproc {
    all e, e': Event | EdgeExists[e, Complete, e', Fetch, uhb_proc] =>
	(NodeExists[e', ViCLCreate] => EdgeExists[e, Complete, e', ViCLCreate, uhb_proc]) and 
	(all e'': Event | ProgramOrder[e', e''] and NodeExists[e'', ViCLCreate] => EdgeExists[e, Complete, e'', ViCLCreate, uhb_proc])
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// branch prediction
fact squash_spec_window_one { all e : Event | all b : MispredictedBranch | (b->e in po) =>
	(
		not NodeExists[e, Commit] and
		EdgeExists[e, ReorderBuffer, b, Execute, usquash] and
		(NodeExists[e, ViCLCreate] => EdgeExists[e, ViCLCreate, b, Execute, usquash])
	)
} 

fact squash_spec_window_two { all e' : Event | all b : MispredictedBranch | (some e : Event | not SameEvent[e, e'] and e->e' in po and b->e in po) =>
	(
		not NodeExists[e', Commit] and
		EdgeExists[e', ReorderBuffer, b, Execute, usquash] and
		(NodeExists[e', ViCLCreate] => EdgeExists[e', ViCLCreate, b, Execute, usquash])
	)
}

fact branch_commit { all b : Branch | (not SpecWindowOne[b] and not SpecWindowTwo[b]) => NodeExists[b, Commit]}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// committeed vs. squashed instructions
fact squashed_event { all e: MemoryEvent |
	(
		IsIllegalRead[e] or
		IsIllegalWrite[e] or
		DependsOnIllegal[e] or 
		ReadsFromIllegal[e] or
		SpecWindowOne[e] or
		SpecWindowTwo[e] or
		(some e' :  Event | ProgramOrder[e, e'] and (some e'': Event | ProgramOrder[e'', e] and (HasDependency[e'', e'] or e''->e' in rf) and IsIllegalRead[e''] or IsIllegalWrite[e'']))
	) <=> not NodeExists[e, Commit]
}

fact committed_read { all r:  { Read + CacheFlush } |
	(
		not IsIllegalRead[r] and
		not DependsOnIllegal[r] and
		not ReadsFromIllegal[r] and
		not SpecWindowOne[r]	 and
		not SpecWindowTwo[r]	 and
		(no e' :  Event | ProgramOrder[r, e'] and (some e'': Event | ProgramOrder[e'', r] and (HasDependency[e'', e'] or e''->e' in rf) and IsIllegalRead[e''] or IsIllegalWrite[e'']))
	) => NodeExists[r, Commit]
}

fact committed_write { all w:  { Write } |
	(
		not IsIllegalWrite[w] and
		not DependsOnIllegal[w] and
		not SpecWindowOne[w] and
		not SpecWindowTwo[w] and	
		(no e' :  Event | ProgramOrder[w, e'] and (some e'': Event | ProgramOrder[e'', w] and (HasDependency[e'', e'] or e''->e' in rf) and IsIllegalRead[e''] or IsIllegalWrite[e'']))
	) => NodeExists[w, Commit]
}

fact depends_on_illegal { all e: Event | all r: Read | (HasDependency[r, e] and IsIllegalRead[r] and not SpecWindowOne[e] and not SpecWindowTwo[e]) <=>  EdgeExists[e, ReorderBuffer, r, PermissionCheck, usquash] }
fact reads_from_illegal { all e: Event | all w : Write | (IsAnyRead[e] and w->e in rf and IsIllegalWrite[w] and not SpecWindowOne[e] and not SpecWindowTwo[e]) <=> EdgeExists[e, ReorderBuffer, w, PermissionCheck, usquash]}

fact vicl_permissions_viclc_pc { all e, e': Event | (EdgeExists[e, ReorderBuffer, e', PermissionCheck, usquash]) => (NodeExists[e, ViCLCreate] => EdgeExists[e, ViCLCreate, e', PermissionCheck, usquash])} 
fact vicl_permissions_rob_pc { all e, e': Event | (EdgeExists[e, ViCLCreate, e', PermissionCheck, usquash]) => (EdgeExists[e, ReorderBuffer, e', PermissionCheck, usquash])} 

fact suqashed_write { all w : Write | not NodeExists[w, Commit]=> not NodeExists[w, StoreBuffer] and not NodeExists[w, MainMemory] and not NodeExists[w, ViCLCreate] and not NodeExists[w, ViCLExpire] }
fact committed_cwrite { all w : CacheableWrite | NodeExists[w, Commit] => NodeExists[w, StoreBuffer] and NodeExists[w, MainMemory] and NodeExists[w, ViCLCreate] and NodeExists[w, ViCLExpire] }
fact committed_ncwrite { all w : NonCacheableWrite | NodeExists[w, Commit] => NodeExists[w, StoreBuffer] and NodeExists[w, MainMemory] }

fact fetch_after_squash { all disj e, e' : Event | (ProgramOrder[e, e'] and not NodeExists[e, Commit] and NodeExists[e', Commit]) <=> EdgeExists[e, Complete, e', Fetch, uhb_spec] }

fact constrain_usquash { all e, e' : Event | all l, l' : Location | EdgeExists[e, l, e', l', usquash] =>
	(not SameEvent[e, e'] and (l in ReorderBuffer or l in ViCLCreate) and not NodeExists[e, Commit]) and
	( (e' in Branch and l' = Execute) or ((IsIllegalRead[e'] or IsIllegalWrite[e']) and l' = PermissionCheck))
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// constrain additional uhb edges
fact bound_urf { urf in 
	Write->Execute->Read->Execute +
	Write->ViCLCreate->Read->Execute +
   	Write->MainMemory->Read->Execute +
	Write->MainMemory->Read->ViCLCreate
}

fact bound_uco { uco in
	Write->ViCLCreate->Write->ViCLCreate +
	Write->ViCLExpire->Write->ViCLCreate +
	Write->MainMemory->Write->MainMemory
}

fact bound_ufr { ufr in
	Read->Execute->Write->Execute +
    Read->ViCLCreate->Write->MainMemory + 
	Read->Execute->Write->MainMemory 
}

fact bound_ustb_flush { ustb_flush in
	Write->ViCLCreate->Read->Execute +
	Write->MainMemory->Read->Execute
}

fact bound_udep { udep in 
	Read->Execute->{MemoryEvent + CacheFlush}->Execute +
	Read->ViCLCreate->MemoryEvent->ViCLCreate
}

fact bound_uhb_spec { uhb_spec in
	Event->Complete->Event->Fetch
}

fact bound_ustb { ustb in
	Read->Execute->Write->ViCLCreate +
	Read->Execute->Write->MainMemory +
	Read->Execute->Write->PermissionCheck
}

fact bound_ufence { ufence in
	 Write->MainMemory->Fence->Execute
}

fact bound_uvicl { uvicl in
	Read->ViCLCreate->Read->Execute + 
	Read->Execute->Read->ViCLExpire + 
	Read->Execute->Write->ViCLExpire
}  

fact bound_ucci { ucci in
	Event->ViCLCreate->Event->ViCLCreate + 
	Event->ViCLExpire->Event->ViCLCreate
}

fact bound_uflush { uflush in
	Event->ViCLExpire->CacheFlush->Execute 
}

fact bound_uhb_proc { uhb_proc in 
	AttackerEvent->Complete->VictimEvent->Fetch + 
	VictimEvent->Complete->AttackerEvent->Fetch +
    AttackerEvent->Complete->VictimEvent->ViCLCreate +
    VictimEvent->Complete->AttackerEvent->ViCLCreate
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

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Threat Descriptions= 
fact explicit_evictions {
	all disj e, e' : CacheableEvent |
			IsAnyRead[e'] and
			(ProgramOrder[e, e'] or EdgeExists[e, Complete, e', Fetch, uhb_proc]) and
			(SameVirtualAddress[e, e'] or SamePhysicalAddress[e, e'] and SameIndexL1[e, e']) and 
			NodeExists[e, ViCLCreate] and
			(no e'' : CacheableEvent | EdgeExists[e, ViCLExpire, e'', ViCLCreate, ucci] and not SameEvent[e'', e']) and
			(no e'' : CacheFlush |  EdgeExists[e, ViCLExpire, e'', Execute, uflush])
	=> IsAnyWrite[e] and EdgeExists[e, ViCLCreate, e', Execute, urf] or IsAnyRead[e] and EdgeExists[e, ViCLCreate, e', Execute, uvicl]
}

pred meltdown_fix { all e: MemoryEvent |	
	(
		not (SpecWindowOne[e] or SpecWindowTwo[e]) and
		(
			IsIllegalRead[e] or
			IsIllegalWrite[e] or
			DependsOnIllegal[e] or
			ReadsFromIllegal[e] or
			(some e' :  Event | ProgramOrder[e, e'] and (some e'': Event | ProgramOrder[e'', e] and (HasDependency[e'', e'] or e''->e' in rf) and IsIllegalRead[e''] or IsIllegalWrite[e'']))
		)
	) => not NodeExists[e, ViCLCreate]
}

pred flush_reload {
	some disj a, a', f : AttackerEvent |

	IsAnyMemory[a] and
	IsAnyRead[a'] and

	NodeExists[a, Commit] and 
	NodeExists[a', Commit] and 
	NodeExists[f, Commit] and

	SameVirtualAddress[a, a'] and
	ProgramOrder[a, a'] and

	ProgramOrder[a, f] and
	ProgramOrder[f, a'] and
	(no e: Event | ProgramOrder[a, e] and ProgramOrder[e, f]) and
	(no e: Event | EdgeExists[a, Complete, e, Fetch, uhb_proc] and EdgeExists[e, Complete, f, Fetch, uhb_proc]) and
	
	IsCacheable[a]  and	
	NodeExists[a, ViCLCreate] and

	IsCacheable[a']  and	
	not NodeExists[a', ViCLCreate] and 

	not (EdgeExists[a, ViCLCreate, a', Execute, urf] and EdgeExists[a', Execute, a, ViCLExpire, uvicl]) and
	not (EdgeExists[a, ViCLCreate, a', Execute, uvicl] and EdgeExists[a', Execute, a, ViCLExpire, uvicl]) and 

	(
		IsCacheFlush[f] and SameVirtualAddress[a, f] or
		IsAnyRead[f] and not SamePhysicalAddress[a, f] and EdgeExists[a, ViCLExpire, f, ViCLCreate, ucci] or 
		IsAnyWrite[f] and not SamePhysicalAddress[a, f] and EdgeExists[a, ViCLExpire, f, ViCLCreate, ucci]
	)
  	and
	not (some e: AttackerEvent |
  		ProgramOrder[f, e] and 
    	ProgramOrder[e, a'] and 
     	SameVirtualAddress[e, a'] and
		IsCacheable[e] and 
		IsAnyMemory[e] and
		NodeExists[e, Commit]) and 	

  	not (some e: AttackerEvent | ProgramOrder[e, a]) and
  	not (some e: AttackerEvent | ProgramOrder[a', e]) and
  	not (some e: Event | EdgeExists[e, Complete, a, Fetch, uhb_proc]) and
  	not (some e: Event | EdgeExists[a', Complete, e, Fetch, uhb_proc])
}

run test_flush_reload {
	shared_ro_mem and
	flush_reload and 
	NumProcessThreads[1, Attacker] and
	NumProcessThreads[1, Victim] and
	#dep = 0 and
	ucheck
} for 57 but 1 Core, 2 Process, 1 CacheIndexL1, 1 Cacheability, 2 Outcome, 4 Address, 2 PhysicalAddress, 2 VirtualAddress, 10 Location, 4 Event, 32 Node

run test_meltdown {
	no_shared_mem and
	flush_reload and 
	#dep = 1 and
	(all disj e, e' : Event | HasDependency[e, e'] => (Victim in PhysicalAddress[e].region and Attacker in PhysicalAddress[e'].region and NodeExists[e', ViCLCreate])) and	
	NumProcessThreads[1, Attacker] and
	NumProcessThreads[0, Victim] and
	ucheck
} for 67 but 1 Core, 2 Process, 2 CacheIndexL1, 1 Cacheability, 2 Outcome, 6 Address, 3 PhysicalAddress, 3 VirtualAddress, 10 Location, 5 Event, 38 Node

run test_spectre {
	no_shared_mem and
	flush_reload and 
	#dep = 1 and
	(all disj e, e' : Event | HasDependency[e, e'] => (Victim in PhysicalAddress[e].region and Attacker in PhysicalAddress[e'].region and NodeExists[e', ViCLCreate])) and
	meltdown_fix and
	NumProcessThreads[1, Attacker] and
	NumProcessThreads[0, Victim] and
	ucheck
} for 75 but 1 Core, 2 Process, 2 CacheIndexL1, 1 Cacheability, 2 Outcome, 6 Address, 3 PhysicalAddress, 3 VirtualAddress, 10 Location, 6 Event, 44 Node
