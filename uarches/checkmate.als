module checkmate

/////////////////////////////////////////////////////////////////////////////////////
// Candidate Executions module
/////////////////////////////////////////////////////////////////////////////////////

sig Core { }

abstract sig Process { }
one sig Attacker extends Process { }
one sig Victim extends Process { }

abstract sig Address { }

abstract sig Cacheability { }
one sig Cacheable extends Cacheability { }
lone sig NonCacheable extends Cacheability { }

sig CacheIndexL1 { }

sig VirtualAddress extends Address { 
	indexL1: one CacheIndexL1,
	map: one PhysicalAddress,
	cacheability: one Cacheability
}
                                
sig PhysicalAddress extends Address {
    readers: set Process,
    writers: set Process,
    region: one Process}

abstract sig Event {	
	po: lone Event,
	NodeRel: set Location,
	
	process: one Process,
	coh: set Event,
   	core: one Core,	

	sub_uhb: set Location->Event->Location,
	urf : set Location->Event->Location,		
	uco : set Location->Event->Location,
	ufr : set Location->Event->Location,
	ustb_flush: set Location->Event->Location,
	udep : set Location->Event->Location,
	uhb_spec : set Location->Event->Location,
	ucoh_inter : set Location->Event->Location,
	ucoh_intra : set Location->Event->Location,
	ustb: set Location->Event->Location,
	uvicl: set Location->Event->Location,		
  	ucci: set Location->Event->Location,
  	usquash: set Location->Event->Location,
  	ufence: set Location->Event->Location,
	uflush: set Location->Event->Location,	
	uhb_inter: set Location->Event->Location,
	uhb_intra: set Location->Event->Location,
	uhb_proc: set Location->Event->Location
}

abstract sig MemoryEvent extends Event {
	address: one VirtualAddress						
}

sig Read extends MemoryEvent {
    dep : set { MemoryEvent + CacheFlush }
}

sig Write extends MemoryEvent {
	rf: set Read,								
	co: set Write, 			
}

abstract sig Fence extends Event { }
sig FenceSC extends Fence { 
	sc: set FenceSC
}

sig CacheFlush extends Event { 
    flush_addr : one VirtualAddress
}

sig Branch extends Event {
	outcome : one Outcome,
	prediction : one Outcome
}

abstract sig Outcome { }
one sig Taken extends Outcome { }
one sig NotTaken extends Outcome { }

//po
fact po_acyclic { acyclic[po] }															
fact po_prior { all e: Event | lone e.~po }											

fun po_loc : MemoryEvent->MemoryEvent { ^po & (address.map).~(address.map) }	

//dep
fact dep_in_po { dep in ^po }				

//com
fun com : MemoryEvent->MemoryEvent { rf + fr + co }								
fact com_in_same_addr { com in (address.map).~(address.map) }						

//writes
fact co_transitive { transitive[co] }													
fact co_total { all a: Address | total[co, a.~(address.map) & Write] }

//reads
fact lone_source_write { rf.~rf in iden }								
fun fr : Read->Write {							
  ~rf.co																							
  +
  ((Read - (Write.rf)) <:  ((address.map).~(address.map)) :> Write)		
}

//rmws
//fact rmw_adjacent { rmw in po & address.~address } // dep & address.~address } 

//fences
fact sc_total { total[sc, FenceSC] }
fun fence_sc : MemoryEvent->MemoryEvent { (MemoryEvent <: *po :> FenceSC).(FenceSC <: *po :> MemoryEvent) }

/////////////////////////////////////////////////////////////////////////////////////
// Check module
/////////////////////////////////////////////////////////////////////////////////////

abstract sig Location { }

sig Node {
	event: one Event,
	loc: one Location,
	uhb: set Node
}

fact { all e, e' : Event | all l, l' : Location | e->l->e'->l' in sub_uhb => ( e->l in NodeRel and e'->l' in NodeRel ) }

// uhb is the union of all u* relations
fact {
			{ 	urf +
         		uco +
				ufr + 
				udep +
				uhb_spec +
				ucoh_inter +
				ucoh_intra +
				ustb +
				ustb_flush +
				uvicl	+
				ucci +
				usquash +
				uflush +
				uhb_inter +
				uhb_intra +
				uhb_proc
			} = sub_uhb
}
	
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
fact { all e, e' : Event 	| all l, l' : Location | EdgeExists[e, l, e', l', uhb_inter] => SameThread[e, e'] }

pred ucheck { acyclic[uhb]  } 					// ucheck is a predicate that requires acyclicity 

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
// =Alloy Check predicates and functions=
fun CoreOf[e: Event] : Event { ( (Event - (Event.po)) & e ) + ( (Event - (Event.po)) & (^po.e) ) }
fun CacheableRead : Read { Read <: address.cacheability.Cacheable }
fun NonCacheableRead : Read { Read <: address.cacheability.NonCacheable }
fun CacheableWrite : Write { Write <: address.cacheability.Cacheable }
fun NonCacheableWrite : Write { Write <: address.cacheability.NonCacheable }
fun CacheableEvent : MemoryEvent { MemoryEvent <: address.cacheability.Cacheable }
fun NonCacheableEvent : MemoryEvent { MemoryEvent <: address.cacheability.NonCacheable }
fun AttackerEvent : Event { process.Attacker }
fun VictimEvent : Event { process.Victim }
fun AttackerRead : Event { Read <: process.Attacker }
fun AttackerWrite : Event { Write <: process.Attacker }
fun VictimRead : Event { Read <: process.Victim }
fun VictimWrite : Event { Write <:  process.Victim }
fun PhysicalAddress[e: Event] : PhysicalAddress { e.address.map + e.flush_addr.map }
fun VirtualAddress[e: Event] : VirtualAddress { e.address + e.flush_addr }
fun PredictedBranch : Branch { ((outcome.~prediction) & iden).Branch }
fun MispredictedBranch : Branch { Branch - ((outcome.~prediction) & iden).Branch }

pred NodeExists[e: Event, l: Location] { e->l in NodeRel }
pred EdgeExists[e: Event, l: Location, e': Event, l': Location, node_rel: Event->Location->Event->Location] 	{ e->l->e'->l' in node_rel }
pred DataFromInitialStateAtPA[r: Read] { r in {Read - Write.rf} }
pred HasDependency[r: Event, e: Event] { r->e in dep}
pred IsAnyMemory[e: Event] { e in MemoryEvent}
pred IsAnyRead[e: Event] { e in Read }
pred IsAnyWrite[e: Event] { e in Write }
pred IsAnyFence[e: Event] { e in Fence }
pred IsAnyBranch[e: Event] { e in Fence }
pred IsCacheFlush[e: Event] { e in CacheFlush }
pred SameProcess[e: Event, e': Event] { e->e' in process.~process }
pred SameCore[e: Event, e': Event] { e->e' in core.~core }
pred SameThread[e: Event, e': Event] { e->e' in ^po + ^~po }
pred SameLocation[l: Location, l': Location] { l->l' in iden }
pred SameEvent[e: Event, e': Event] { e->e' in iden }
pred ProgramOrder[e: Event, e': Event] { e->e' in ^po }
pred IsCacheable[e: MemoryEvent] { (e.address).cacheability = Cacheable }
pred IsIllegalRead[e: MemoryEvent] { (IsAnyRead[e] or IsCacheFlush[e]) and (not (e.process in PhysicalAddress[e].readers)) }
pred IsIllegalWrite[e: MemoryEvent] { IsAnyWrite[e] and (not (e.process in PhysicalAddress[e].writers)) }
pred DependsOnIllegal[e : MemoryEvent] { some r: Read | r->e in dep and IsIllegalRead[r] }
pred ReadsFromIllegal[e : MemoryEvent]  { IsAnyRead[e] and (some w: Write | w->e in rf and IsIllegalWrite[w]) }
pred SameIndexL1 [e: Event, e': Event] { (e.address).indexL1 = (e'.address).indexL1 }
pred NumProcessThreads[i: Int, P: Process] { #((Event - (Event.po)) & process.P)=i }
pred NumThreads[i: Int] { #(Event - (Event.po))=i }

pred SamePhysicalAddress[e: Event, e': Event] {
    e->e' in (address.map).~(address.map) or
	e->e' in (flush_addr.map).~(address.map) or
	e->e' in (address.map).~(flush_addr.map) or
	e->e' in (flush_addr.map).~(flush_addr.map)
} 

pred SameVirtualAddress[e: Event, e': Event] { 
    e->e' in address.~address or
	e->e' in flush_addr.~address or
	e->e' in address.~flush_addr or
    e->e' in flush_addr.~flush_addr
}

pred SameSourcingWrite[r: Read, r': Read] {
	not SameEvent[r, r'] and (
		DataFromInitialStateAtPA[r] and DataFromInitialStateAtPA[r'] or	// sourced by the same initial value
    	r->r' in ~rf.rf 
	)
}

