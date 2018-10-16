module FiveStage
open checkmate_simple

/////////////////////////////////////////////////////////////////////////////////////
// Pipeline module
/////////////////////////////////////////////////////////////////////////////////////

// define pipeline locations
one sig FetchStage extends Location { }	
one sig DecodeStage extends Location { }
one sig ExecuteStage extends Location { }
one sig MemoryStage extends Location { }	
one sig WritebackStage extends Location { }
one sig StoreBuffer extends Location { }	
one sig MemoryHierarchy extends Location { }

// uhb_intra is limitted to reads path and writes path
fact 	{ all f : Fence	| all disj l, l' : Location | l->l' in f_path <=> EdgeExists[f, l, f, l', uhb_intra] }
fact 	{ all r : Read 	| all disj l, l' : Location | l->l' in r_path <=> EdgeExists[r, l, r, l', uhb_intra] }
fact 	{ all w : Write	| all disj l, l' : Location | l->l' in w_path <=> EdgeExists[w, l, w, l', uhb_intra] }

// create minimal nodes
// all nodes that *must exist* 
fact {
	Fence->{ FetchStage + DecodeStage + ExecuteStage + MemoryStage + WritebackStage } +	
	Read->{ FetchStage + DecodeStage + ExecuteStage + MemoryStage + WritebackStage } +	
	Write->{ FetchStage + DecodeStage + ExecuteStage + MemoryStage + WritebackStage + StoreBuffer + MemoryHierarchy }  in NodeRel
}	

// bound nodes so Alloy doesn't create more
// all nodes that *could exist*
fact { NodeRel in 
	Fence->{ FetchStage + DecodeStage + ExecuteStage + MemoryStage + WritebackStage } +
	Read->{ FetchStage + DecodeStage + ExecuteStage + MemoryStage + WritebackStage } +																	
	Write->{ FetchStage + DecodeStage + ExecuteStage + MemoryStage + WritebackStage + StoreBuffer + MemoryHierarchy } 
}

// define read path
fun f_path : Location->Location {
 	FetchStage->DecodeStage +
	DecodeStage->ExecuteStage +
	ExecuteStage->MemoryStage +
	MemoryStage->WritebackStage
}	

// define read path
fun r_path : Location->Location {
 	FetchStage->DecodeStage +
	DecodeStage->ExecuteStage +
	ExecuteStage->MemoryStage +
	MemoryStage->WritebackStage
}	

// define write path
fun w_path : Location->Location { 
	FetchStage->DecodeStage +
	DecodeStage->ExecuteStage +
	ExecuteStage->MemoryStage +
	MemoryStage->WritebackStage +
	WritebackStage->StoreBuffer +
	StoreBuffer->MemoryHierarchy
} 	

// uhb_inter: inter-instruction happens-beofre
fact Fetch_stage_is_inorder { all disj e, e' : Event 	|
	ProgramOrder[e, e'] <=>
	EdgeExists[e, FetchStage, e', FetchStage, uhb_inter]
}

fact Decode_stage_is_inorder { all disj e, e' : Event |
	EdgeExists[e, FetchStage, e', FetchStage, uhb_inter] <=>
	EdgeExists[e, DecodeStage, e', DecodeStage, uhb_inter]
}

fact Execute_stage_is_inorder { all disj e, e' : Event |
	EdgeExists[e, DecodeStage, e', DecodeStage, uhb_inter] <=>
 	EdgeExists[e, ExecuteStage, e', ExecuteStage, uhb_inter]
}

fact Memory_stage_is_inorder { all disj e, e' : Event	|
	EdgeExists[e, ExecuteStage, e', ExecuteStage, uhb_inter] <=>
	EdgeExists[e, MemoryStage, e', MemoryStage, uhb_inter]
}

fact Writeback_stage_is_inorder { all disj e, e' : Event |
	EdgeExists[e, MemoryStage, e', MemoryStage, uhb_inter ]	<=>
	EdgeExists[e, WritebackStage, e', WritebackStage, uhb_inter]
}

fact STB_FIFO { all disj w, w' : Write 	|
	EdgeExists[w, WritebackStage, w', WritebackStage, uhb_inter] <=>
	EdgeExists[w, StoreBuffer, w', StoreBuffer, uhb_inter]
}

fact STB_OneAtATime { all disj w, w' : Write |
	EdgeExists[w, StoreBuffer, w', StoreBuffer, uhb_inter] <=>
	EdgeExists[w, MemoryHierarchy, w', StoreBuffer, uhb_inter]
}

// limit uhb_inter to edges that make sense to constrain Alloy
fact { uhb_inter in 
	Event->FetchStage->Event->FetchStage + 
	Event->DecodeStage->Event->DecodeStage + 
	Event->ExecuteStage->Event->ExecuteStage +
	Event->MemoryStage->Event->MemoryStage +
	Event->WritebackStage->Event->WritebackStage +
	Write->StoreBuffer->Write->StoreBuffer +
	Write->MemoryHierarchy->Write->StoreBuffer 
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Predicates=

// true if read is sourced from STB
// i.e., if it executes before the write reaches the L1 Cache
pred STBFwd[w: Write, r: Read] {
   	SameCore[w, r] and
	ProgramOrder[w, r] and
   	EdgeExists[w, MemoryStage, r, MemoryStage, urf] and
	EdgeExists[r, MemoryStage, w, MemoryHierarchy, ustb]
}

// true if all stores before read have been written to the L1 Cache
pred STBEmpty[r: Read] {
    all w : Write | SameAddress[w, r] and ProgramOrder[w, r] => 
	(
		EdgeExists[w, MemoryHierarchy, r, MemoryStage, urf] 
	) 
}

// rf: reads from MainMemory
// describes relations in urf
pred ReadSourcedFromMM[w: Write, r: Read] {
	EdgeExists[w, MemoryHierarchy, r, MemoryStage, urf]
}

pred Coherence[w: Write, w': Write] {
   	EdgeExists[w, MemoryHierarchy, w', MemoryHierarchy, uco]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Axioms=
fact mfence_order { 
	all f: Fence | all w : Write |
	SameCore[w, f] and 
	ProgramOrder[w, f] <=>
    EdgeExists[w, MemoryHierarchy, f, ExecuteStage, ufence]
}

fact ReadsFrom {
	 all r : Read | all w : Write | w->r in rf  =>
    (
	   	STBFwd[w, r] or	
														
       	STBEmpty[r] and (	 ReadSourcedFromMM[w, r] )

	)
}

fact CoherenceOrder {
    all w : Write | all w' : Write| w->w' in co =>	// TODO: double arrow should be fine, but check
    (
        Coherence[w, w']
    )
  
}

fact FromReads {
 	all r : Read | all w : Write | r->w in fr =>
    (
		(SameCore[r, w] and EdgeExists[r, MemoryStage, w, ExecuteStage, ufr]) or
        (not SameCore[r, w] and EdgeExists[r, MemoryStage, w, MemoryHierarchy, ufr] and not EdgeExists[r, MemoryStage, w, ExecuteStage, ufr])
	)

}

// extra constraints to bound edges
fact { urf in 
	Write->MemoryStage->Read->MemoryStage +
	Write->MemoryHierarchy->Read->MemoryStage
}

fact { uco in
	Write->MemoryHierarchy->Write->MemoryHierarchy
}

fact { ufr in
	Read->MemoryStage->Write->MemoryHierarchy +
    Read->MemoryStage->Write->ExecuteStage 
}

fact { ustb in
	Read->MemoryStage->Write->MemoryHierarchy 
}

fact { ufence in
	Write->MemoryHierarchy->Fence->ExecuteStage
}

fact { 
	all w : Write | all r : Read | 	all l, l' : Location |
	EdgeExists[w, l, r, l', urf] => w->r in rf
}

fact {
	all disj w, w' : Write | all l, l' : Location | 
	EdgeExists[w, l, w', l', uco] => w->w' in co
}

fact {
	all r : Read | all w : Write | all l, l' : Location |
	EdgeExists[r, l, w, l', ufr] => r->w in fr
}

fact {
        all r : Read, w : Write | all l, l' : Location |
        EdgeExists[r, l, w, l', ustb] => w->r in rf and STBFwd[w, r]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Tests=

pred sb {
        // test bounds
        #Write=2 and 
        #Read=2 and
        #Fence=0 and 
        #Address=2 and

        // po and com relations                                                                          
        #po=2 and 
        #rf=0 and 
        #fr=2 and 
        #co=0 and                                                                                        
        
        // test description
        NumThreads[2] and
        (
            some disj w0,w1 : Write |
            some disj r0,r1 : Read |
            w0->r0 in po and
            w1->r1 in po and
            r0->w1 in fr and
	        r1->w0 in fr
        )
}

run test_sb {
        sb and
        ucheck
} for 37 but 2 Address, 4 Event, 7 Location 
