(* SPDX-License-Identifier: MIT *)
(* LPS 727298f3: the shared L6 templates the hops hand off to, and the batch data recorded after
   them, in the new launch layout and size bounds.

   The hops start from the FI8 holes' end states.  An FX hole's end bound is its computed start's
   plus the launch's extra reserved pair ([APC.resx_bytes HAT], which the FX ledger counts once
   more; [PlanRegen.fx_end]) plus the recorded growth, and a computed start carries that extra once
   more for each FX hole before it on its chain.  So each end state's total-size bound exceeds that
   of its recorded form (moved by the launch, [HAReg.mregk]/[HAReg.mreg]) by an amount of its own,
   computed here from the states ([DRIFT], the largest over the hops' start states).  The templates,
   shared by every chain, were recorded with the old end bound: their total-size bound, and that of
   every batch state recorded after them, moves by the launch's [HAReg.DT] and by [DRIFT]; the other
   three bounds move by the launch alone; their launch facts are relaunched as [HAReg.mreg] does.
   Their numbering: [HAReg.V_F].  Every hop and every batch job re-runs its check on the states so
   mapped. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan PlanRegen.
From OSSVerify.Proofs.openssl.hashtable.lib Require HAReg.
From OSSVerify.Proofs.openssl.hashtable.lib Require
  FIEndA0se7 FIEndA0so FIEndA1se7 FIEndA1so FIEndA2se7 FIEndA3se7 FIEndA3so FIEndB0se7 FIEndB0so FIEndB1se7
  FIEndB1so FIEndB2se7 FIEndB3se7 FIEndB3so FIEndK10A0 FIEndK10A1 FIEndK10A2 FIEndK10A3 FIEndK10B0 FIEndK10B1
  FIEndK10B2 FIEndK10B3 FIEndK1A0 FIEndK1A1 FIEndK1A2 FIEndK1A3 FIEndK1B0 FIEndK1B1 FIEndK1B2 FIEndK1B3
  FIEndK2A0 FIEndK2A1 FIEndK2A2 FIEndK2A3 FIEndK2B0 FIEndK2B1 FIEndK2B2 FIEndK2B3 FIEndK3A0 FIEndK3A1
  FIEndK3A2 FIEndK3A3 FIEndK3B0 FIEndK3B1 FIEndK3B2 FIEndK3B3 FIEndK4A0 FIEndK4A1 FIEndK4A2 FIEndK4A3
  FIEndK4B0 FIEndK4B1 FIEndK4B2 FIEndK4B3 FIEndK5A0 FIEndK5A1 FIEndK5A2 FIEndK5A3 FIEndK5B0 FIEndK5B1
  FIEndK5B2 FIEndK5B3 FIEndK6A0 FIEndK6A1 FIEndK6A2 FIEndK6A3 FIEndK6B0 FIEndK6B1 FIEndK6B2 FIEndK6B3
  FIEndK7A0 FIEndK7A1 FIEndK7A2 FIEndK7A3 FIEndK7B0 FIEndK7B1 FIEndK7B2 FIEndK7B3 FIEndK8A0 FIEndK8A1
  FIEndK8A2 FIEndK8A3 FIEndK8B0 FIEndK8B1 FIEndK8B2 FIEndK8B3 FIEndK9A0 FIEndK9A1 FIEndK9A2 FIEndK9A3
  FIEndK9B0 FIEndK9B1 FIEndK9B2 FIEndK9B3.
Import ListNotations. Import AX2. Import APC. Import CAP.
Open Scope Z_scope.

(* each hop's start state (an FI8 hole's end state) and its recorded form *)
Definition hop_srcs : list (acs * acs) := [
  (FIEndK10A0.fiendk10a0e_ tt, FIEndK10A0.fiendk10a0_ tt);
  (FIEndK10A1.fiendk10a1e_ tt, FIEndK10A1.fiendk10a1_ tt);
  (FIEndK10A2.fiendk10a2e_ tt, FIEndK10A2.fiendk10a2_ tt);
  (FIEndK10A3.fiendk10a3e_ tt, FIEndK10A3.fiendk10a3_ tt);
  (FIEndK10B0.fiendk10b0e_ tt, FIEndK10B0.fiendk10b0_ tt);
  (FIEndK10B1.fiendk10b1e_ tt, FIEndK10B1.fiendk10b1_ tt);
  (FIEndK10B2.fiendk10b2e_ tt, FIEndK10B2.fiendk10b2_ tt);
  (FIEndK10B3.fiendk10b3e_ tt, FIEndK10B3.fiendk10b3_ tt);
  (FIEndK1A0.fiendk1a0e_ tt, FIEndK1A0.fiendk1a0_ tt);
  (FIEndK1A1.fiendk1a1e_ tt, FIEndK1A1.fiendk1a1_ tt);
  (FIEndK1A2.fiendk1a2e_ tt, FIEndK1A2.fiendk1a2_ tt);
  (FIEndK1A3.fiendk1a3e_ tt, FIEndK1A3.fiendk1a3_ tt);
  (FIEndK1B0.fiendk1b0e_ tt, FIEndK1B0.fiendk1b0_ tt);
  (FIEndK1B1.fiendk1b1e_ tt, FIEndK1B1.fiendk1b1_ tt);
  (FIEndK1B2.fiendk1b2e_ tt, FIEndK1B2.fiendk1b2_ tt);
  (FIEndK1B3.fiendk1b3e_ tt, FIEndK1B3.fiendk1b3_ tt);
  (FIEndK2A0.fiendk2a0e_ tt, FIEndK2A0.fiendk2a0_ tt);
  (FIEndK2A1.fiendk2a1e_ tt, FIEndK2A1.fiendk2a1_ tt);
  (FIEndK2A2.fiendk2a2e_ tt, FIEndK2A2.fiendk2a2_ tt);
  (FIEndK2A3.fiendk2a3e_ tt, FIEndK2A3.fiendk2a3_ tt);
  (FIEndK2B0.fiendk2b0e_ tt, FIEndK2B0.fiendk2b0_ tt);
  (FIEndK2B1.fiendk2b1e_ tt, FIEndK2B1.fiendk2b1_ tt);
  (FIEndK2B2.fiendk2b2e_ tt, FIEndK2B2.fiendk2b2_ tt);
  (FIEndK2B3.fiendk2b3e_ tt, FIEndK2B3.fiendk2b3_ tt);
  (FIEndK3A0.fiendk3a0e_ tt, FIEndK3A0.fiendk3a0_ tt);
  (FIEndK3A1.fiendk3a1e_ tt, FIEndK3A1.fiendk3a1_ tt);
  (FIEndK3A2.fiendk3a2e_ tt, FIEndK3A2.fiendk3a2_ tt);
  (FIEndK3A3.fiendk3a3e_ tt, FIEndK3A3.fiendk3a3_ tt);
  (FIEndK3B0.fiendk3b0e_ tt, FIEndK3B0.fiendk3b0_ tt);
  (FIEndK3B1.fiendk3b1e_ tt, FIEndK3B1.fiendk3b1_ tt);
  (FIEndK3B2.fiendk3b2e_ tt, FIEndK3B2.fiendk3b2_ tt);
  (FIEndK3B3.fiendk3b3e_ tt, FIEndK3B3.fiendk3b3_ tt);
  (FIEndK4A0.fiendk4a0e_ tt, FIEndK4A0.fiendk4a0_ tt);
  (FIEndK4A1.fiendk4a1e_ tt, FIEndK4A1.fiendk4a1_ tt);
  (FIEndK4A2.fiendk4a2e_ tt, FIEndK4A2.fiendk4a2_ tt);
  (FIEndK4A3.fiendk4a3e_ tt, FIEndK4A3.fiendk4a3_ tt);
  (FIEndK4B0.fiendk4b0e_ tt, FIEndK4B0.fiendk4b0_ tt);
  (FIEndK4B1.fiendk4b1e_ tt, FIEndK4B1.fiendk4b1_ tt);
  (FIEndK4B2.fiendk4b2e_ tt, FIEndK4B2.fiendk4b2_ tt);
  (FIEndK4B3.fiendk4b3e_ tt, FIEndK4B3.fiendk4b3_ tt);
  (FIEndK5A0.fiendk5a0e_ tt, FIEndK5A0.fiendk5a0_ tt);
  (FIEndK5A1.fiendk5a1e_ tt, FIEndK5A1.fiendk5a1_ tt);
  (FIEndK5A2.fiendk5a2e_ tt, FIEndK5A2.fiendk5a2_ tt);
  (FIEndK5A3.fiendk5a3e_ tt, FIEndK5A3.fiendk5a3_ tt);
  (FIEndK5B0.fiendk5b0e_ tt, FIEndK5B0.fiendk5b0_ tt);
  (FIEndK5B1.fiendk5b1e_ tt, FIEndK5B1.fiendk5b1_ tt);
  (FIEndK5B2.fiendk5b2e_ tt, FIEndK5B2.fiendk5b2_ tt);
  (FIEndK5B3.fiendk5b3e_ tt, FIEndK5B3.fiendk5b3_ tt);
  (FIEndK6A0.fiendk6a0e_ tt, FIEndK6A0.fiendk6a0_ tt);
  (FIEndK6A1.fiendk6a1e_ tt, FIEndK6A1.fiendk6a1_ tt);
  (FIEndK6A2.fiendk6a2e_ tt, FIEndK6A2.fiendk6a2_ tt);
  (FIEndK6A3.fiendk6a3e_ tt, FIEndK6A3.fiendk6a3_ tt);
  (FIEndK6B0.fiendk6b0e_ tt, FIEndK6B0.fiendk6b0_ tt);
  (FIEndK6B1.fiendk6b1e_ tt, FIEndK6B1.fiendk6b1_ tt);
  (FIEndK6B2.fiendk6b2e_ tt, FIEndK6B2.fiendk6b2_ tt);
  (FIEndK6B3.fiendk6b3e_ tt, FIEndK6B3.fiendk6b3_ tt);
  (FIEndK7A0.fiendk7a0e_ tt, FIEndK7A0.fiendk7a0_ tt);
  (FIEndK7A1.fiendk7a1e_ tt, FIEndK7A1.fiendk7a1_ tt);
  (FIEndK7A2.fiendk7a2e_ tt, FIEndK7A2.fiendk7a2_ tt);
  (FIEndK7A3.fiendk7a3e_ tt, FIEndK7A3.fiendk7a3_ tt);
  (FIEndK7B0.fiendk7b0e_ tt, FIEndK7B0.fiendk7b0_ tt);
  (FIEndK7B1.fiendk7b1e_ tt, FIEndK7B1.fiendk7b1_ tt);
  (FIEndK7B2.fiendk7b2e_ tt, FIEndK7B2.fiendk7b2_ tt);
  (FIEndK7B3.fiendk7b3e_ tt, FIEndK7B3.fiendk7b3_ tt);
  (FIEndK8A0.fiendk8a0e_ tt, FIEndK8A0.fiendk8a0_ tt);
  (FIEndK8A1.fiendk8a1e_ tt, FIEndK8A1.fiendk8a1_ tt);
  (FIEndK8A2.fiendk8a2e_ tt, FIEndK8A2.fiendk8a2_ tt);
  (FIEndK8A3.fiendk8a3e_ tt, FIEndK8A3.fiendk8a3_ tt);
  (FIEndK8B0.fiendk8b0e_ tt, FIEndK8B0.fiendk8b0_ tt);
  (FIEndK8B1.fiendk8b1e_ tt, FIEndK8B1.fiendk8b1_ tt);
  (FIEndK8B2.fiendk8b2e_ tt, FIEndK8B2.fiendk8b2_ tt);
  (FIEndK8B3.fiendk8b3e_ tt, FIEndK8B3.fiendk8b3_ tt);
  (FIEndK9A0.fiendk9a0e_ tt, FIEndK9A0.fiendk9a0_ tt);
  (FIEndK9A1.fiendk9a1e_ tt, FIEndK9A1.fiendk9a1_ tt);
  (FIEndK9A2.fiendk9a2e_ tt, FIEndK9A2.fiendk9a2_ tt);
  (FIEndK9A3.fiendk9a3e_ tt, FIEndK9A3.fiendk9a3_ tt);
  (FIEndK9B0.fiendk9b0e_ tt, FIEndK9B0.fiendk9b0_ tt);
  (FIEndK9B1.fiendk9b1e_ tt, FIEndK9B1.fiendk9b1_ tt);
  (FIEndK9B2.fiendk9b2e_ tt, FIEndK9B2.fiendk9b2_ tt);
  (FIEndK9B3.fiendk9b3e_ tt, FIEndK9B3.fiendk9b3_ tt);
  (FIEndA0se7.fienda0se7e_ tt, FIEndA0se7.fienda0se7_ tt);
  (FIEndA0so.fienda0soe_ tt, FIEndA0so.fienda0so_ tt);
  (FIEndA1se7.fienda1se7e_ tt, FIEndA1se7.fienda1se7_ tt);
  (FIEndA1so.fienda1soe_ tt, FIEndA1so.fienda1so_ tt);
  (FIEndA2se7.fienda2se7e_ tt, FIEndA2se7.fienda2se7_ tt);
  (FIEndA3se7.fienda3se7e_ tt, FIEndA3se7.fienda3se7_ tt);
  (FIEndA3so.fienda3soe_ tt, FIEndA3so.fienda3so_ tt);
  (FIEndB0se7.fiendb0se7e_ tt, FIEndB0se7.fiendb0se7_ tt);
  (FIEndB0so.fiendb0soe_ tt, FIEndB0so.fiendb0so_ tt);
  (FIEndB1se7.fiendb1se7e_ tt, FIEndB1se7.fiendb1se7_ tt);
  (FIEndB1so.fiendb1soe_ tt, FIEndB1so.fiendb1so_ tt);
  (FIEndB2se7.fiendb2se7e_ tt, FIEndB2se7.fiendb2se7_ tt);
  (FIEndB3se7.fiendb3se7e_ tt, FIEndB3se7.fiendb3se7_ tt);
  (FIEndB3so.fiendb3soe_ tt, FIEndB3so.fiendb3so_ tt)
  ].
Definition DRIFT : Z := Eval vm_compute in
  fold_left (fun m p => Z.max m (a_totsz (fst p) - a_totsz (snd p))) hop_srcs 0.
Definition DTL : Z := HAReg.DT + DRIFT.
Definition mregT (S : acs) : acs :=
  resize DTL HAReg.DY HAReg.DE HAReg.DA (relaunch NX0 HAReg.D_OLD HAReg.L_NEW S).
Definition mplanT (p : plan) : plan := pshs (fun v => v) mregT None true p.
Definition mregV (S : acs) : acs :=
  resize DTL HAReg.DY HAReg.DE HAReg.DA (relaunch NX0 HAReg.D_OLD HAReg.L_NEW (ash HAReg.V_F S)).
Definition mplanV (p : plan) : plan := pshs HAReg.V_F mregV None true p.
