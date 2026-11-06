(* Rtt102CutCheck.v: prints the ELABORATED BODIES of Rtt102Cut.v's cut predicates and stretch statements with every
   implicit argument shown and notations off, so the class-implicit FPState resolution can be read off the bodies
   (the text owner's rule and its amendment, 2026-10-29: `Print`, `Set Printing Implicit`, `Unset Printing Notations`;
   `About` / `Check` print only the type). A statement binds a second FPState (the cut's fxc); the class position
   must hold the entry fx everywhere and fxc only an explicit argument. No lemma. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102Cut.
Set Printing Implicit.
Set Printing Width 4000.
Unset Printing Notations.
Print rtt_led.
Print rtt_wout.
Print rtt_Qx.
Print rtt_rb.
Print rtt_Q.
Print rtt_fx.
Print rtt_J.
Print rtt_carry.
Print rtt_at_pjw.
Print rtt_at_txe.
Print rtt_at_x.
Print rtt_at_cmp.
Print rtt_at_o2.
Print rtt_at_ck.
Print rtt_seg.
Print rtt_seg_entry.
Print rtt_post.
Print rtt_pre.
Set Printing Notations.
Unset Printing Implicit.
(* the exported lemmas exist in the .vo (Locate against the compiled file, not git grep), and their axioms *)
Locate rtt_count_le.
Locate rtt_capacity_of_len.
Locate rtt_capacity.
Locate rtt_text_of_seg.
Locate rtt_text_of_segs.
Print Assumptions rtt_capacity.
Print Assumptions rtt_text_of_segs.
