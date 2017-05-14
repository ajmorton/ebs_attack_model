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
// Precondition: 
//   - engine_mode is ModeOff
//
// Postcondition: 
//   - bus now contains the EngineOn message
//   - engine_mode is now ModeOn
//   - last_action is SendEngineOn
//   - and nothing else changes
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
//   - bus contains EngineOnMessage
//   - ebs_mode is ModeOff
//
// Postcondition: 
//   - bus is now empty
//   - ebs_mode is now ModeOn
//   - last_action is RecvEngineOn
//   - and nothing else changes
pred recv_engine_on[s, s' : State] {
 
	// preconditions
	s.bus = EngineOnMessage and
	s.ebs_mode = ModeOff and

	// postcondition changed
	s'.bus = s.bus - EngineOnMessage and
	s'.ebs_mode = ModeOn and
	s'.last_action = RecvEngineOn and

	// postcondition unchanged
	s'.foot_pressure = s.foot_pressure and 
	s'.engine_mode = s.engine_mode and
	s'.brake_pressure = s.brake_pressure

}

// Models the action in which a BrakePressureUpdate CAN Bus message is sent
// from the brake pedal onto the CAN Bus, containing the current
// foot pressure applied to the brake.
// Precondition: 
//   - bus is empty
//
// Postcondition: 
//   - bus now contains BrakePressureUpdateMessage, with correct pressure field
//   - last_action is SendBrakePressureUpdate
//   - and nothing else changes
pred send_brake_pressure_update[s, s' : State] {

	// preconditions
	no s.bus and
	
	// postconditions changed
	let msg = BrakePressureUpdateMessage | 
	msg.pressure = s.foot_pressure and
	s'.bus = msg and
	
	s'.last_action = SendBrakePressureUpdate and 

	// postcondition unchanged
	s'.ebs_mode = s.ebs_mode and
	s'.foot_pressure = s.foot_pressure and
	s'.engine_mode = s.engine_mode and
	s'.brake_pressure = s.brake_pressure

}

// Models the action in which a BrakePressureUpdate CAN Bus message is received
// by the Brake Controller, causing the current brake pressure to be updated
// to that contained in the message and the message to be removed from the bus.
// Precondition: 
//   - bus contains BrakePressureUpdateMessage
//   - ebs_mode is ModeOn
//   - last_action is SendBrakePressureUpdate
//
// Postcondition: 
//   - bus is now empty
//   - brake_pressure is now s.bus.pressure
//   - last_action is RecvBrakePressureUpdate
//   - and nothing else changes
pred recv_brake_pressure_update[s, s' : State] {
  
	// preconditions
	s.bus = BrakePressureUpdateMessage and

	// postcondition changed
	s'.bus = s.bus - BrakePressureUpdateMessage and
	s'.last_action = RecvBrakePressureUpdate and

	// postcondition unchanged
	s'.foot_pressure = s.foot_pressure and
	s'.engine_mode = s.engine_mode and
	s'.ebs_mode = s.ebs_mode and
	
	// brake_pressure update rule: update if ebs_mode is on, otherwise don't
	(
		(s.ebs_mode = ModeOn  and s'.brake_pressure = s.bus.pressure ) or
		(s.ebs_mode = ModeOff and s'.brake_pressure = s.brake_pressure)
	)

}

// Models the action in which the amount of foot pressure applied by the
// driver to the brake pedal changes
// Precondition: 
//   - none
//
// Postcondition: 
//   - foot_pressure changes arbitrarily (is totally unconstrained)
//   - last_action is ChangeFootPressure
//   - and nothing else changes
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
// Attacker's abilities: 
//		Can utilise replay attack by changing the bus to any previous message,
//		can also delete messages from the bus
//
// Precondition: 
//   - none
//
// Postcondition: 
//   - bus contains a previous message, or is now empty
//   - last_action is AttackerAction
//   - and nothing else changes
pred attacker_action[s, s' : State] {

	// attacker capabilities, replay a previous message or delete message from bus
	(s'.bus in ord/prevs[s].bus or
 	 no s'.bus) and
	
	// last action updated
  s'.last_action = AttackerAction and

	// everything else unchanged
  s'.ebs_mode = s.ebs_mode and
  s'.brake_pressure = s.brake_pressure and
  s'.foot_pressure = s.foot_pressure and
  s'.engine_mode = s.engine_mode
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
 // or attacker_action[s,s']
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

// From assignment 1: If the EBS is off then brake pressure is always at max. 
// This predicate models that.
pred recv_brake_pressure_update_safety [s : State] {
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
// The assertion holds as this functionality was modeled explicitly into 
// recv_brake_update_message. 


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
// The assertion didn't hold pre MACing, but afterwards does. 
// This is because the attacker can no longer fabricate an engineOn message 
// while the engine is still off. Post MACing an engineOn message can only 
// come from turning the engine on



// Gives a precise enough specification of what value the brake_pressure field
// should have, given the prior receipt of BrakePressureUpdate CAN Bus messages,
// so that attacks under the updated attacker model (see the Assignment 3
// instructions) can be diagnosed by Alloy
//
// The predicate states that if there is a change in the bus between two states,
// and either of the states contained a BrakePressureUpdateMessage, then
// changes between state must satisfy one of three requirements:
// - a valid BrakePressureUpdateMessage (BPUmsg) was placed on an empty bus,
//   with a pressure field equal to the previous states foot_pressure
// - a BPUmsg was removed from the bus, and the subsequent brake pressure was
//   modified (or not) dependant on the current ebs_mode
//
// Because bus modification has been verified by this predicate, correct brake 
// pressure updates are also verified: BPUmsg's added to the bus must have the 
// correct pressure field, and on BPUmsg removal the correct actions are also 
// taken with respect to the (already verified) pressure fields.
// By extension, correct brake_pressure is verified. 
assert brake_at_correct_pressure {
	  all s : State | all s' : ord/next[s] | 
		// a change in the bus
		s'.bus != s.bus and 
		// where either state contains a BrakePressureUpdateMessage
		some ((s.bus + s'.bus) & BrakePressureUpdateMessage) 

		// implies one of:
		implies
			(
				// a valid BPUmsg addition
				(no s.bus and s'.bus.pressure = s.foot_pressure)  or	
				// a valid BPUmsg removal ebs_mode on
				(s.ebs_mode = ModeOn  and no s'.bus and s'.brake_pressure = s.bus.pressure) or
				// a valid BPUmsg removal ebs_mode off
				(s.ebs_mode = ModeOff and no s'.bus and s'.brake_pressure = s.brake_pressure) //or
			)
}

// NOTE: you will want to adjust these thresholds for your own use
check brake_at_correct_pressure for 3 but 8 State

// Attacks still permitted by the updated attacker model:
// 
// Replay attacks (resending old MACed bus messages) are still possible for the 
// attacker, although detectable by Alloy via brake_at_correct_pressure.
// These would allow an attacker to apply the brakes (or not) at inopportune 
// times for the driver.
//
// Unwanted deletion of messages from the bus is still possible; 
// Currently only deletion of BrakePressureUpdate messages is detected by Alloy 
// (via brake_at_correct_pressure), but a small extension to the predicate could
// identify deletions of an EngineOn message also
//
// A form of DDoS attack could also be implemented by the attacker: continually 
// placing a message on the bus such that the system cannot add their own messages.
// This is once again detectable only for BrakePressureUpdate messages in the 
// current implementation.


// Relationship to our HAZOP study:
//
// ** NB : The numbers mentioned below refer to the line items in the HAZOP study submitted
//             as a part of assignment 2. Link to the document : http://expozit.com/HAZOPS.xlsx
//
// Which attacks are covered by our HAZOP?
//	- Replay attacks
//		Broadly covered by line item 115 "Messages are sent without action by a principal"
//		Although Replay attacks were not specificly considered when writing the item
//
//	- Deletion
//		Once again broadly covered by line item 109 "No message is sent". 
//		The difference between a message being sent, then deleted before being recieved, 
//		and a message not being sent at all is largely semantic. In the context of 
//		the Ada system  
//
//	- DDoS
//		Denial of service was not accounted for. Some items of similar effect 
//		(109 above, 110 "Too many messages sent", and 115 above) are present.
//
// New hazards discovered by this model:
//	- DDoS
//		A DDoS attack doesn't fit cleanly into a particular guideword. 
//		It either qualifies as a NONE (as no message can be added to the bus), 
//		or as a MORE (due to too many messages being added to the bus), or 
//		perhaps even OTHER THAN (messages other than the intended are sent to the bus).
//		The associated design item would be "In response to input from a principal, 
//		a corresponding message is sent on the CANBus"
