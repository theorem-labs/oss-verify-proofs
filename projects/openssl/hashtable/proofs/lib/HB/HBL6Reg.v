(* SPDX-License-Identifier: MIT *)
(* LPS 727298f3: the shared L6 templates the hops hand off to, and the batch data recorded after
   them, in the new launch layout and size bounds.

   The hops start from the FI8 holes' end states.  An FX hole's end bound is its computed start's
   plus the launch's extra reserved pair ([APC.resx_bytes HAT], which the FX ledger counts once
   more; [PlanRegen.fx_end]) plus the recorded growth, and a computed start carries that extra once
   more for each FX hole before it on its chain.  So each end state's total-size bound exceeds that
   of its recorded form (moved by the launch, [HBReg.mregk]/[HBReg.mreg]) by an amount of its own,
   computed here from the states ([DRIFT], the largest over the hops' start states).  The templates,
   shared by every chain, were recorded with the old end bound: their total-size bound, and that of
   every batch state recorded after them, moves by the launch's [HBReg.DT] and by [DRIFT]; the other
   three bounds move by the launch alone; their launch facts are relaunched as [HBReg.mreg] does.
   Their numbering: [HBReg.V_F].  Every hop and every batch job re-runs its check on the states so
   mapped. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan PlanRegen.
From OSSVerify.Proofs.openssl.hashtable.lib Require HBReg.
From OSSVerify.Proofs.openssl.hashtable.lib Require
  BFIEndA0se7 BFIEndA0so BFIEndA1se7 BFIEndA1so BFIEndA2se7 BFIEndA3se7 BFIEndA3so BFIEndB0se7 BFIEndB0so BFIEndB1se7
  BFIEndB1so BFIEndB2se7 BFIEndB3se7 BFIEndB3so BFIEndK10A0 BFIEndK10A1 BFIEndK10A2 BFIEndK10A3 BFIEndK10B0 BFIEndK10B1
  BFIEndK10B2 BFIEndK10B3 BFIEndK1A0 BFIEndK1A1 BFIEndK1A2 BFIEndK1A3 BFIEndK1B0 BFIEndK1B1 BFIEndK1B2 BFIEndK1B3
  BFIEndK2A0 BFIEndK2A1 BFIEndK2A2 BFIEndK2A3 BFIEndK2B0 BFIEndK2B1 BFIEndK2B2 BFIEndK2B3 BFIEndK3A0 BFIEndK3A1
  BFIEndK3A2 BFIEndK3A3 BFIEndK3B0 BFIEndK3B1 BFIEndK3B2 BFIEndK3B3 BFIEndK4A0 BFIEndK4A1 BFIEndK4A2 BFIEndK4A3
  BFIEndK4B0 BFIEndK4B1 BFIEndK4B2 BFIEndK4B3 BFIEndK5A0 BFIEndK5A1 BFIEndK5A2 BFIEndK5A3 BFIEndK5B0 BFIEndK5B1
  BFIEndK5B2 BFIEndK5B3 BFIEndK6A0 BFIEndK6A1 BFIEndK6A2 BFIEndK6A3 BFIEndK6B0 BFIEndK6B1 BFIEndK6B2 BFIEndK6B3
  BFIEndK7A0 BFIEndK7A1 BFIEndK7A2 BFIEndK7A3 BFIEndK7B0 BFIEndK7B1 BFIEndK7B2 BFIEndK7B3 BFIEndK8A0 BFIEndK8A1
  BFIEndK8A2 BFIEndK8A3 BFIEndK8B0 BFIEndK8B1 BFIEndK8B2 BFIEndK8B3 BFIEndK9A0 BFIEndK9A1 BFIEndK9A2 BFIEndK9A3
  BFIEndK9B0 BFIEndK9B1 BFIEndK9B2 BFIEndK9B3.
Import ListNotations. Import AX2. Import APC. Import CAP.
Open Scope Z_scope.

(* each hop's start state (an FI8 hole's end state) and its recorded form *)
Definition hop_srcs : list (acs * acs) := [
  (BFIEndK10A0.fiendk10a0e_ tt, BFIEndK10A0.fiendk10a0_ tt);
  (BFIEndK10A1.fiendk10a1e_ tt, BFIEndK10A1.fiendk10a1_ tt);
  (BFIEndK10A2.fiendk10a2e_ tt, BFIEndK10A2.fiendk10a2_ tt);
  (BFIEndK10A3.fiendk10a3e_ tt, BFIEndK10A3.fiendk10a3_ tt);
  (BFIEndK10B0.fiendk10b0e_ tt, BFIEndK10B0.fiendk10b0_ tt);
  (BFIEndK10B1.fiendk10b1e_ tt, BFIEndK10B1.fiendk10b1_ tt);
  (BFIEndK10B2.fiendk10b2e_ tt, BFIEndK10B2.fiendk10b2_ tt);
  (BFIEndK10B3.fiendk10b3e_ tt, BFIEndK10B3.fiendk10b3_ tt);
  (BFIEndK1A0.fiendk1a0e_ tt, BFIEndK1A0.fiendk1a0_ tt);
  (BFIEndK1A1.fiendk1a1e_ tt, BFIEndK1A1.fiendk1a1_ tt);
  (BFIEndK1A2.fiendk1a2e_ tt, BFIEndK1A2.fiendk1a2_ tt);
  (BFIEndK1A3.fiendk1a3e_ tt, BFIEndK1A3.fiendk1a3_ tt);
  (BFIEndK1B0.fiendk1b0e_ tt, BFIEndK1B0.fiendk1b0_ tt);
  (BFIEndK1B1.fiendk1b1e_ tt, BFIEndK1B1.fiendk1b1_ tt);
  (BFIEndK1B2.fiendk1b2e_ tt, BFIEndK1B2.fiendk1b2_ tt);
  (BFIEndK1B3.fiendk1b3e_ tt, BFIEndK1B3.fiendk1b3_ tt);
  (BFIEndK2A0.fiendk2a0e_ tt, BFIEndK2A0.fiendk2a0_ tt);
  (BFIEndK2A1.fiendk2a1e_ tt, BFIEndK2A1.fiendk2a1_ tt);
  (BFIEndK2A2.fiendk2a2e_ tt, BFIEndK2A2.fiendk2a2_ tt);
  (BFIEndK2A3.fiendk2a3e_ tt, BFIEndK2A3.fiendk2a3_ tt);
  (BFIEndK2B0.fiendk2b0e_ tt, BFIEndK2B0.fiendk2b0_ tt);
  (BFIEndK2B1.fiendk2b1e_ tt, BFIEndK2B1.fiendk2b1_ tt);
  (BFIEndK2B2.fiendk2b2e_ tt, BFIEndK2B2.fiendk2b2_ tt);
  (BFIEndK2B3.fiendk2b3e_ tt, BFIEndK2B3.fiendk2b3_ tt);
  (BFIEndK3A0.fiendk3a0e_ tt, BFIEndK3A0.fiendk3a0_ tt);
  (BFIEndK3A1.fiendk3a1e_ tt, BFIEndK3A1.fiendk3a1_ tt);
  (BFIEndK3A2.fiendk3a2e_ tt, BFIEndK3A2.fiendk3a2_ tt);
  (BFIEndK3A3.fiendk3a3e_ tt, BFIEndK3A3.fiendk3a3_ tt);
  (BFIEndK3B0.fiendk3b0e_ tt, BFIEndK3B0.fiendk3b0_ tt);
  (BFIEndK3B1.fiendk3b1e_ tt, BFIEndK3B1.fiendk3b1_ tt);
  (BFIEndK3B2.fiendk3b2e_ tt, BFIEndK3B2.fiendk3b2_ tt);
  (BFIEndK3B3.fiendk3b3e_ tt, BFIEndK3B3.fiendk3b3_ tt);
  (BFIEndK4A0.fiendk4a0e_ tt, BFIEndK4A0.fiendk4a0_ tt);
  (BFIEndK4A1.fiendk4a1e_ tt, BFIEndK4A1.fiendk4a1_ tt);
  (BFIEndK4A2.fiendk4a2e_ tt, BFIEndK4A2.fiendk4a2_ tt);
  (BFIEndK4A3.fiendk4a3e_ tt, BFIEndK4A3.fiendk4a3_ tt);
  (BFIEndK4B0.fiendk4b0e_ tt, BFIEndK4B0.fiendk4b0_ tt);
  (BFIEndK4B1.fiendk4b1e_ tt, BFIEndK4B1.fiendk4b1_ tt);
  (BFIEndK4B2.fiendk4b2e_ tt, BFIEndK4B2.fiendk4b2_ tt);
  (BFIEndK4B3.fiendk4b3e_ tt, BFIEndK4B3.fiendk4b3_ tt);
  (BFIEndK5A0.fiendk5a0e_ tt, BFIEndK5A0.fiendk5a0_ tt);
  (BFIEndK5A1.fiendk5a1e_ tt, BFIEndK5A1.fiendk5a1_ tt);
  (BFIEndK5A2.fiendk5a2e_ tt, BFIEndK5A2.fiendk5a2_ tt);
  (BFIEndK5A3.fiendk5a3e_ tt, BFIEndK5A3.fiendk5a3_ tt);
  (BFIEndK5B0.fiendk5b0e_ tt, BFIEndK5B0.fiendk5b0_ tt);
  (BFIEndK5B1.fiendk5b1e_ tt, BFIEndK5B1.fiendk5b1_ tt);
  (BFIEndK5B2.fiendk5b2e_ tt, BFIEndK5B2.fiendk5b2_ tt);
  (BFIEndK5B3.fiendk5b3e_ tt, BFIEndK5B3.fiendk5b3_ tt);
  (BFIEndK6A0.fiendk6a0e_ tt, BFIEndK6A0.fiendk6a0_ tt);
  (BFIEndK6A1.fiendk6a1e_ tt, BFIEndK6A1.fiendk6a1_ tt);
  (BFIEndK6A2.fiendk6a2e_ tt, BFIEndK6A2.fiendk6a2_ tt);
  (BFIEndK6A3.fiendk6a3e_ tt, BFIEndK6A3.fiendk6a3_ tt);
  (BFIEndK6B0.fiendk6b0e_ tt, BFIEndK6B0.fiendk6b0_ tt);
  (BFIEndK6B1.fiendk6b1e_ tt, BFIEndK6B1.fiendk6b1_ tt);
  (BFIEndK6B2.fiendk6b2e_ tt, BFIEndK6B2.fiendk6b2_ tt);
  (BFIEndK6B3.fiendk6b3e_ tt, BFIEndK6B3.fiendk6b3_ tt);
  (BFIEndK7A0.fiendk7a0e_ tt, BFIEndK7A0.fiendk7a0_ tt);
  (BFIEndK7A1.fiendk7a1e_ tt, BFIEndK7A1.fiendk7a1_ tt);
  (BFIEndK7A2.fiendk7a2e_ tt, BFIEndK7A2.fiendk7a2_ tt);
  (BFIEndK7A3.fiendk7a3e_ tt, BFIEndK7A3.fiendk7a3_ tt);
  (BFIEndK7B0.fiendk7b0e_ tt, BFIEndK7B0.fiendk7b0_ tt);
  (BFIEndK7B1.fiendk7b1e_ tt, BFIEndK7B1.fiendk7b1_ tt);
  (BFIEndK7B2.fiendk7b2e_ tt, BFIEndK7B2.fiendk7b2_ tt);
  (BFIEndK7B3.fiendk7b3e_ tt, BFIEndK7B3.fiendk7b3_ tt);
  (BFIEndK8A0.fiendk8a0e_ tt, BFIEndK8A0.fiendk8a0_ tt);
  (BFIEndK8A1.fiendk8a1e_ tt, BFIEndK8A1.fiendk8a1_ tt);
  (BFIEndK8A2.fiendk8a2e_ tt, BFIEndK8A2.fiendk8a2_ tt);
  (BFIEndK8A3.fiendk8a3e_ tt, BFIEndK8A3.fiendk8a3_ tt);
  (BFIEndK8B0.fiendk8b0e_ tt, BFIEndK8B0.fiendk8b0_ tt);
  (BFIEndK8B1.fiendk8b1e_ tt, BFIEndK8B1.fiendk8b1_ tt);
  (BFIEndK8B2.fiendk8b2e_ tt, BFIEndK8B2.fiendk8b2_ tt);
  (BFIEndK8B3.fiendk8b3e_ tt, BFIEndK8B3.fiendk8b3_ tt);
  (BFIEndK9A0.fiendk9a0e_ tt, BFIEndK9A0.fiendk9a0_ tt);
  (BFIEndK9A1.fiendk9a1e_ tt, BFIEndK9A1.fiendk9a1_ tt);
  (BFIEndK9A2.fiendk9a2e_ tt, BFIEndK9A2.fiendk9a2_ tt);
  (BFIEndK9A3.fiendk9a3e_ tt, BFIEndK9A3.fiendk9a3_ tt);
  (BFIEndK9B0.fiendk9b0e_ tt, BFIEndK9B0.fiendk9b0_ tt);
  (BFIEndK9B1.fiendk9b1e_ tt, BFIEndK9B1.fiendk9b1_ tt);
  (BFIEndK9B2.fiendk9b2e_ tt, BFIEndK9B2.fiendk9b2_ tt);
  (BFIEndK9B3.fiendk9b3e_ tt, BFIEndK9B3.fiendk9b3_ tt);
  (BFIEndA0se7.fienda0se7e_ tt, BFIEndA0se7.fienda0se7_ tt);
  (BFIEndA0so.fienda0soe_ tt, BFIEndA0so.fienda0so_ tt);
  (BFIEndA1se7.fienda1se7e_ tt, BFIEndA1se7.fienda1se7_ tt);
  (BFIEndA1so.fienda1soe_ tt, BFIEndA1so.fienda1so_ tt);
  (BFIEndA2se7.fienda2se7e_ tt, BFIEndA2se7.fienda2se7_ tt);
  (BFIEndA3se7.fienda3se7e_ tt, BFIEndA3se7.fienda3se7_ tt);
  (BFIEndA3so.fienda3soe_ tt, BFIEndA3so.fienda3so_ tt);
  (BFIEndB0se7.fiendb0se7e_ tt, BFIEndB0se7.fiendb0se7_ tt);
  (BFIEndB0so.fiendb0soe_ tt, BFIEndB0so.fiendb0so_ tt);
  (BFIEndB1se7.fiendb1se7e_ tt, BFIEndB1se7.fiendb1se7_ tt);
  (BFIEndB1so.fiendb1soe_ tt, BFIEndB1so.fiendb1so_ tt);
  (BFIEndB2se7.fiendb2se7e_ tt, BFIEndB2se7.fiendb2se7_ tt);
  (BFIEndB3se7.fiendb3se7e_ tt, BFIEndB3se7.fiendb3se7_ tt);
  (BFIEndB3so.fiendb3soe_ tt, BFIEndB3so.fiendb3so_ tt)
  ].
Definition DRIFT : Z := Eval vm_compute in
  fold_left (fun m p => Z.max m (a_totsz (fst p) - a_totsz (snd p))) hop_srcs 0.
Definition DTL : Z := HBReg.DT + DRIFT.
Definition mregT (S : acs) : acs :=
  resize DTL HBReg.DY HBReg.DE HBReg.DA (relaunch NX0 HBReg.D_OLD HBReg.L_NEW S).
Definition mplanT (p : plan) : plan := pshs (fun v => v) mregT None true p.
Definition mregV (S : acs) : acs :=
  resize DTL HBReg.DY HBReg.DE HBReg.DA (relaunch NX0 HBReg.D_OLD HBReg.L_NEW (ash HBReg.V_F S)).
Definition mplanV (p : plan) : plan := pshs HBReg.V_F mregV None true p.
