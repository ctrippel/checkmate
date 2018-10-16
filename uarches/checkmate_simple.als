module checkmate_simple

/////////////////////////////////////////////////////////////////////////////////////
// Candidate Executions module
/////////////////////////////////////////////////////////////////////////////////////

sig Address { }

abstract sig Event {	
	po: lone Event,	

	NodeRel: set Location,

	urf : set Location->Event->Location,		
	uco : set Location->Event->Location,
	ufr : set Location->Event->Location,

	ustb: set Location->Event->Location,
	ufence: set Location->Event->Location,

	uhb_inter: set Location->Event->Location,
	uhb_intra: set Location->Event->Location,

	sub_uhb: set Location->Event->Location
}

abstract sig MemoryEvent extends Event {
	address: one Address							
}

sig Read extends MemoryEvent {
	//rmw: lone Write,
	//dep: set Event
}

sig Write extends MemoryEvent {
	rf: set Read,				
	co: set Write, 
}

abstract sig Fence extends Event { }
sig mfence extends Fence { }

//po
fact po_acyclic { acyclic[po] }															
fact po_prior { all e: Event | lone e.~po }											

fun po_loc : MemoryEvent->MemoryEvent { ^po & address.~address }		

// dep	
// fact dep_in_po { dep in ^po }	

//com
fun com : MemoryEvent->MemoryEvent { rf + fr + co }								
fact com_in_same_addr { com in address.~address }							

//writes
fact co_transitive { transitive[co] }													
fact co_total { all a: Address | total[co, a.~address & Write] }	

//reads
fact lone_source_write { rf.~rf in iden }								
fun fr : Read->Write {							
  ~rf.co																							
  +
  ((Read - (Write.rf)) <:  (address.~address) :> Write)		
}

fact no_trailing_fence { all f : Fence | f in Event.po and f in po.Event }

// rmws
// fact rmw_adjacent { rmw in po & address.~address } // dep & address.~address } 

/////////////////////////////////////////////////////////////////////////////////////
// Check module
/////////////////////////////////////////////////////////////////////////////////////
abstract sig Location { }

sig Node {
	event: one Event,
	loc: one Location,
	uhb: set Node
}

// uhb only relates Nodes
fact { all e, e' : Event | all l, l' : Location | e->l->e'->l' in sub_uhb => ( e->l in NodeRel and e'->l' in NodeRel ) }

// uhb is the union of all u* relations
fact { { urf + uco + ufr + ustb + ufence + uhb_inter + uhb_intra } = sub_uhb }

// no iden in uhb
fact { all e, e' : Event | all l, l' : Location | e->e' in iden and l->l' in iden => not e->l->e'->l' in sub_uhb  }

// node mapping
fact { all e : Event | all l : Location  | e->l in NodeRel => one n : Node | n.event = e and n.loc = l }
fact { all n : Node | n.event->n.loc in NodeRel }
fact { all n, n' : Node | n->n' in uhb <=> n.event->n.loc->n'.event->n'.loc in sub_uhb }

// uhb_intra only relates the same event to different locations
fact 	{ all e, e' : Event 	| all l, l' : Location |  EdgeExists[e, l, e', l', uhb_intra] => SameEvent[e, e'] }

// uhb_inter only relates different events on the same core
fact { all e, e' : Event 	| all l, l' : Location | EdgeExists[e, l, e', l', uhb_inter] => not SameEvent[e, e'] }
fact { all e, e' : Event 	| all l, l' : Location | EdgeExists[e, l, e', l', uhb_inter] => SameCore[e, e'] }

pred ucheck { acyclic[uhb]  }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy shortcuts=
fun optional[f: univ->univ] : univ->univ  { iden + f }
pred transitive[rel: Event->Event]        { rel.rel in rel }	
pred irreflexive[rel: Event->Event]       { no iden & rel }
pred irreflexive[rel: Node->Node]       { no iden & rel }
pred acyclic[rel: Event->Event]           { irreflexive[^rel] }
pred acyclic[rel: Node->Node]           { irreflexive[^rel] } 
pred total[rel: Event->Event, bag: Event] {
  all disj e, e': bag | e->e' in rel + ~rel	
  acyclic[rel]											
}
pred u_irreflexive[node_rel: Event->Location->Event->Location]       {
	no node_rel or (		all e, e': Event |
								all l, l': Location |
								e->l->e'->l' in node_rel => not ( (e->e') in iden and (l->l') in iden )
							)
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy uspec predicates and functions=
fun CoreOf[e: Event] : Event { ( (Event - (Event.po)) & e ) + ( (Event - (Event.po)) & (^po.e) ) }
fun Address[e: Event] : Address { e.address }

pred IsAnyMemory[e: Event] { e in MemoryEvent}
pred IsAnyRead[e: Event] { e in Read }
pred IsAnyWrite[e: Event] { e in Write }
pred IsAnyFence[e: Event] { e in Fence }
// pred HasDependency[r: Read, e: Event] { r->e in dep}
pred SameEvent[e: Event, e': Event] { e->e' in iden }
pred SameLocation[l: Location, l': Location] { l->l' in iden }
pred SameCore[e: Event, e': Event] { e->e' in ^po + ^~po }
pred ProgramOrder[e: Event, e': Event] { e->e' in ^po }
pred DataFromInitialStateAtPA[r: Read] { r in {Read - Write.rf} }
pred SameAddress[e: Event, e': Event] { e->e' in address.~address }
pred NodeExists[e: Event, l: Location] { e->l in NodeRel }
pred EdgeExists[e: Event, l: Location, e': Event, l': Location, node_rel: Event->Location->Event->Location] 	{ e->l->e'->l' in node_rel }
pred NumThreads[i: Int] { #(Event - (Event.po))=i }
pred SameSourcingWrite[r: Read, r': Read] {
	not SameEvent[r, r'] and SameAddress[r, r'] and (
		DataFromInitialStateAtPA[r] and DataFromInitialStateAtPA[r'] or	// sourced by the same initial value
    	r->r' in ~rf.rf 
	)

}
