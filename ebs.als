// ===========================================================================
// SWEN90010 2017 - Assignment 3 Submission
// by Andrew Morton 522139, Bishal Sapkota 854950 
// ===========================================================================

module ebs
open util/ordering[State] as ord

// =========================== System State ==================================
// an abstract signature for CAN Bus messages
abstract sig Message {}

// a type for storing amounts of Brake Pressure
sig BrakePressure {}

// maximum brake pressure
one sig MaxBrakePressure extends BrakePressure {}

// BrakePressureUpdate CAN Bus messages
sig BrakePressureUpdateMessage extends Message {
  pressure : BrakePressure
}

// EngineOn CAN Bus message
one sig EngineOnMessage extends Message {}

// Modes: either On or Off
abstract sig Mode {}
one sig ModeOn, ModeOff extends Mode {}

// meta information in the model that identifies the last action performed
abstract sig Action {}
one sig SendEngineOn, RecvEngineOn, AttackerAction,
        ChangeFootPressure, SendBrakePressureUpdate, 
        RecvBrakePressureUpdate extends Action {}

// The system state
sig State {
  bus : lone Message,              // CAN Bus state: holds up to one message
  ebs_mode : Mode,                 // whether EBS system is in on or off mode
  foot_pressure : BrakePressure,   // current amount of foot pressure applied 
                                   //  to brake pedal by the driver
  engine_mode : Mode,              // whether the engine is on or off
  brake_pressure : BrakePressure,  // current brake pressure (applied to wheel)
  last_action : lone Action,       // identifies the most
                                   //  recent action performed
}

// an axiom that restricts the model to never allow more than one messasge on
// the CAN Bus at a time; a simplifying assumption to ease the analysis
fact {
  all s : State | lone s.bus
}

// =========================== Initial State =================================

// The initial state of the system:
//   - empty CAN Bus, 
//   - EBS and Engine both off
//   - Brake at maximum pressure
pred Init[s : State] {
  no s.bus and s.ebs_mode = ModeOff and s.engine_mode = ModeOff
  and s.brake_pressure = MaxBrakePressure and
  no s.last_action
}

// =========================== Actions =======================================

// Models the action in which the Engine is turned on, causing
// the EngineOn message to be sent on the CAN Bus
// Precondition: engine is off
// Postcondition: CAN Bus now contains the EngineOn message
//                Engine is now On
//                last_action is SendEngineOn
//                and nothing else changes
pred send_engine_on[s, s' : State] {
  s.engine_mode = ModeOff and
  s'.bus = s.bus + EngineOnMessage and
  s'.ebs_mode = s.ebs_mode and
  s'.foot_pressure = s.foot_pressure and
  s'.brake_pressure = s.brake_pressure and
  s'.engine_mode = ModeOn and
  s'.last_action = SendEngineOn
}

// Models the action in which the EngineOn message is received by the
// Brake Controller, causing the EBS system's mode to change from Off to On
// and the message to be removed from the CAN Bus
// Precondition: 
//		bus contains EngineOnMessage
//		ebs_mode is ModeOff
//****		engine_mode is ModeOn *** ignore in naïve model
//****		last_action is SendEngineOn ****
//		
// Postcondition: 
//		bus is now empty
//		ebs_mode is ModeOn
//		last_action is RecvEngineOn
//   and nothing else changes
pred recv_engine_on[s, s' : State] {
  // preconditions
	s.bus         = EngineOnMessage and
	s.ebs_mode    = ModeOff         and

	// post changes
	s'.bus         = s.bus - EngineOnMessage and
	s'.ebs_mode    = ModeOn                  and
	s'.last_action = RecvEngineOn            and

	// post not changed
	s'.foot_pressure  = s.foot_pressure  and 
	s'.engine_mode    = s.engine_mode    and
	s'.brake_pressure = s.brake_pressure

}

// Models the action in which a BrakePressureUpdate CAN Bus message is sent
// from the brake pedal onto the CAN Bus, containing the current
// foot pressure applied to the brake.
// Precondition: 
//		bus is empty
//		note: we chose not to include eng/ebs mode on as that is covered  by recvBPupdate
// Postcondition: 
//		bus now contains BrakePressureUpdateMessage, w/ specified pressure equal to init foot_pressure
//		last_action is SendBrakePressureUpdate
//    and nothing else changes
pred send_brake_pressure_update[s, s' : State] {
  //preconditions
	no s.bus and
	
	// postconditions changes
	// **** SYYYNTAXXXX
	let msg = BrakePressureUpdateMessage | 
	msg.pressure = s.foot_pressure and

	s'.bus = msg and

	s'.last_action = SendBrakePressureUpdate and 

	// postcondition same
	s'.ebs_mode = s.ebs_mode and
	s'.foot_pressure = s.foot_pressure and
	s'.engine_mode = s.engine_mode and
	s'.brake_pressure = s.brake_pressure

}

// Models the action in which a BrakePressureUpdate CAN Bus message is received
// by the Brake Controller, causing the current brake pressure to be updated
// to that contained in the message and the message to be removed from the bus.
// Precondition: 
//		bus contains BrakePressureUpdateMessage
//		ebs_mode is ModeOn
//		last_action is SendBrakePressureUpdate

// Postcondition: 
//		bus is now empty
//		brake_pressure is now s.bus.pressure
//    last_action is RecvBrakePressureUpdate
//    and nothing else changes
pred recv_brake_pressure_update[s, s' : State] {
  // pre
	s.bus = BrakePressureUpdateMessage and
	s.last_action = SendBrakePressureUpdate and

	// post changes
	s'.bus = s.bus - BrakePressureUpdateMessage and
	
	s'.last_action = RecvBrakePressureUpdate and

	// post unchanged
	s'.foot_pressure = s.foot_pressure and
	s'.engine_mode = s.engine_mode and
	s'.ebs_mode = s.ebs_mode and
	
	((s.ebs_mode = ModeOn  and s'.brake_pressure = s.bus.pressure ) or
	(s.ebs_mode = ModeOff and s'.brake_pressure = s.brake_pressure))

}

// Models the action in which the amount of foot pressure applied by the
// driver to the brake pedal changes
// Precondition: none
// Postcondition: foot pressure changes arbitrarily (is totally unconstrained)
//                last_action is ChangeFootPressure
//                and nothing else changes
pred change_foot_pressure[s, s' : State] {
  s'.ebs_mode = s.ebs_mode and
  s'.engine_mode = s.engine_mode and
  s'.last_action = ChangeFootPressure and
  s'.brake_pressure = s.brake_pressure and
  s'.bus = s.bus
}

// =========================== Attacker Actions ==============================

// Models the actions of a potential attacker that has access to the CAN Bus
// The only part of the system state that the attacker can possibly change
// is that of the CAN Bus. 
//
// NOTE: In the initial template you are given, the attacker
// is modelled as being able to modify the bus contents arbitrarily.
// Howeever, for later parts of the assignment you will change this definition
// to only permit certain kinds of modifications to the state of the CAN Bus.
// When doing so, ensure you update the following line that describes the
// attacker's abilities.
//
// Attacker's abilities: 
//		can reset bus to any previous bus message
//
// Precondition: none
// Postcondition: bus state changes in accordance with attacker's abilities
//                last_action is AttackerAction
//                and nothing else changes
pred attacker_action[s, s' : State] {
	(s'.bus in ord/prevs[s].bus or
 	 no s'.bus) and
  s'.ebs_mode = s.ebs_mode and
  s'.brake_pressure = s.brake_pressure and
  s'.foot_pressure = s.foot_pressure and
  s'.engine_mode = s.engine_mode and
  s'.last_action = AttackerAction
}


// =========================== State Transitions and Traces ==================

// State transitions occur via the various actions of the system above
// including those of the attacker.
pred state_transition[s, s' : State] {
  send_engine_on[s,s']
  or recv_engine_on[s,s']
  or change_foot_pressure[s,s']
  or send_brake_pressure_update[s,s']
  or recv_brake_pressure_update[s,s']
  or attacker_action[s,s']
}

// Define the linear ordering on states to be that generated by the
// state transitions above, defining execution traces to be sequences
// of states in which each state follows in the sequence from the last
// by a state transition.
fact state_transition_ord {
  all s: State, s': ord/next[s] {
    state_transition[s,s'] and s' != s
  }
}

// The initial state is first in the order, i.e. all execution traces
// that we model begin in the initial state described by the Init predicate
fact init_state {
  all s: ord/first {
    Init[s]
  }
}

// =========================== Properties ====================================

// An example assertion and check:
// Specifies that once the EBS is in the On mode, it never leaves
// the On mode in all future states in the execution trace, 
// i.e. it stays in the On mode forever.
assert ebs_never_off_after_on {
  all s : State | all s' : ord/nexts[s] | 
     s.ebs_mode = ModeOn implies s'.ebs_mode = ModeOn
}

check ebs_never_off_after_on for 5 expect 0


// Specifies a simple safety property taken from the Assignment 1 requirements
// about when the recv_brake_pressure_update action is allowed to occur
pred recv_brake_pressure_update_safety [s : State] {
// TODO add a comment to justify 
  s.ebs_mode = ModeOff implies s.brake_pressure = MaxBrakePressure
}

// Asserts that the above property always holds whenever recv_brake_pressure
// occurs
assert recv_brake_pressure_update_safe {
  all s, s' : State | recv_brake_pressure_update[s,s'] implies
    recv_brake_pressure_update_safety[s]
}

// NOTE: you will want to use smaller thresholds if getting
//       counterexamples, so you can interpret them
check recv_brake_pressure_update_safe for 10
// <FILL IN HERE: does the assertion hold? why / why not?>


// Describes a basic sanity condition of the system: the EBS should be in
// the On mode only when the Engine is also in the On mode. This condition
// should be true in all states of the system, i.e. it should be an "invariant"
pred inv[s : State] {
	s.ebs_mode = ModeOn implies s.engine_mode = ModeOn
}

// Specifies that the invariant "inv" above should be true in all states
// of all execution traces of the system
assert inv_always {
  inv[ord/first] and all s : ord/nexts[ord/first] | inv[s]
  // NOTE (as a curiosity): the above is equivalent to saying
  // all s : State | inv[s]
  // This is because when checking this assertion, the linear order
  // defined on States causes all States considered by Alloy to come
  // from the linear order
}

// Check that the invariant is never violated during 15
// state transitions
// 
// NOTE: you will want to use smaller thresholds if getting
//       counterexamples, so you can interpret them
check inv_always for 15
// <EXPAND ON THIS> Atacker can turn on EBS w/o engine being on


// Gives a precise enough specification of what value the brake_pressure field
// should have, given the prior receipt of BrakePressureUpdate CAN Bus messages,
// so that attacks under the updated attacker model (see the Assignment 3
// instructions) can be diagnosed by Alloy
//
// <FILL IN HERE (describe your predicate)>
assert brake_at_correct_pressure {
  // <FILL IN HERE>
}

// NOTE: you will want to adjust these thresholds for your own use
check brake_at_correct_pressure for 3 but 8 State

// Attacks still permitted by the updated attacker model:
// 
// <FILL IN HERE>


// Relationship to our HAZOP study:
//
// <FILL IN HERE>
