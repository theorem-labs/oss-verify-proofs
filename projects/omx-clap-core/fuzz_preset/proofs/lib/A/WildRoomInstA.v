(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/WildRoomInstA.v, with its module paths and numbers changed; 14 of its 49 lines of code are new or changed. *)
(* Theorem Labs, 2026-10: fuzz_preset A' (fuzz_preset.asan, ELF sha256 bff8519bbe3ea0e4), THE SATISFIABILITY WITNESSES
   of the room conjunct of the trace carrier P'' at image A's universe lib/A/ACej.v (the trace-carrier form; blob
   9c1da4e01665 since prh_univ_closure's clause 5 added 78 fixed traces, 98 -> 176, so u_wmax 3998 -> 3920; it was
   f707fd5a39dd, as at a working branch 460396d4bd13) (a Theorem Labs lane's VERIFY rule 1, ruled 22:54Z).
   rule 24: no function proved. rule 24: proves no function (kind: instance facts).
   ONE IMAGE: this file Requires image A's universe and driver traces only (ACej, AF0m); image B's are
   lib/AU/WildRoomInstB.v. The image-free parts (K_LLVMF, init_depot_nil, wild_room_init_K, wild_room_run_fits, cw_of,
   wild_room_cw_fix / _init / _stored) are lib/Reusable/YCbqGwild.v's.
   The start state is YG00.v init_state (lib/A/AD1v.v:125 `AR tfibsegs B ly init_state ..` at univwiden 460396d4bd13),
   whose depot is [] (YCbqGwild.init_depot_nil). Before the first entry call the driver stores only DRV_TRACES
   (lib/A/AF0m.v), all fixed in ACej's universe (drv_fixed_A; lib/A/AD2l.v's TfibB_syms does the same computation
   against the list form). CW_A w1 w2 is the cursor set: parse_items' and parse_string's frees ([0x53878; 0x87764] /
   [0x53878; 0x87e50], the internal file UNIVERSE-PER-RUN.md section 2) followed by the word the unwinder reads (on A' the code word, the
   return site of pj_parse's `jal parse_value`); the witnesses hold for every word. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ACej AF0m.
Import ListNotations.
Local Open Scope Z_scope.

(* the room ACej's universe leaves for wild traces: DEPOT_MAX - |u_fix| (YG01.v univ_of) *)
Lemma A_wmax : u_wmax ACej.Tfib_universe = 3920%nat.
Proof. vm_compute. reflexivity. Qed.
(* THE ENTRY ROOM at the start state: YCbqGwild.K_LLVMF fresh slots *)
Lemma wild_room_run_fits_A : (4 * YCbqGwild.K_LLVMF <= u_wmax ACej.Tfib_universe)%nat.
Proof. rewrite A_wmax. unfold YCbqGwild.K_LLVMF. lia. Qed.
Lemma wild_room_init_A : YCbqGwild.wild_room ACej.Tfib_universe [] YCbqGwild.K_LLVMF (st_depot init_state).
Proof. apply YCbqGwild.wild_room_init_K, YCbqGwild.wild_room_run_fits, wild_room_run_fits_A. Qed.
(* the driver's traces are fixed, so its depot before the first entry call has the same room *)
Lemma drv_fixed_A : forall t, In t AF0m.DRV_TRACES -> In t (u_fix ACej.Tfib_universe).
Proof.
intros t Ht. apply mem_trace_In.
assert (R : forallb (fun t0 => mem_trace t0 (u_fix ACej.Tfib_universe)) AF0m.DRV_TRACES = true)
  by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) R t Ht).
Qed.
Lemma wild_room_drv_A : forall d, incl d AF0m.DRV_TRACES ->
  YCbqGwild.wild_room ACej.Tfib_universe [] YCbqGwild.K_LLVMF d.
Proof.
intros d Hd. apply YCbqGwild.wild_room_fixed; [intros t Ht; exact (drv_fixed_A t (Hd t Ht)) |].
cbn [length]. exact (YCbqGwild.wild_room_run_fits _ wild_room_run_fits_A).
Qed.
(* THE CURSOR SET of a pj_parse call on A' *)
Definition CW_A (w1 w2 : Z) : list (list Z) := YCbqGwild.cw_of ACej.Tfib_wild w1 w2.
Lemma CW_A_fits : forall w1 w2, (length (CW_A w1 w2) <= u_wmax ACej.Tfib_universe)%nat.
Proof. intros w1 w2. unfold CW_A. rewrite YCbqGwild.cw_of_length, A_wmax. lia. Qed.
Lemma wild_room_cw_A : forall w1 w2 d, (forall t, In t d -> In t (u_fix ACej.Tfib_universe) \/ In t (CW_A w1 w2)) ->
  YCbqGwild.wild_room ACej.Tfib_universe (CW_A w1 w2) 0 d.
Proof. intros w1 w2 d Hd. exact (YCbqGwild.wild_room_cw_fix _ _ _ Hd (CW_A_fits w1 w2)). Qed.
(* the witnesses: at the start state, CW not stored yet; and both of CW's traces stored *)
Lemma wild_room_cw_init_A : forall w1 w2, YCbqGwild.wild_room ACej.Tfib_universe (CW_A w1 w2) 0 (st_depot init_state).
Proof. intros w1 w2. exact (YCbqGwild.wild_room_cw_init _ _ (CW_A_fits w1 w2)). Qed.
Lemma wild_room_cw_stored_A : forall w1 w2, YCbqGwild.wild_room ACej.Tfib_universe (CW_A w1 w2) 0 (CW_A w1 w2).
Proof. intros w1 w2. exact (YCbqGwild.wild_room_cw_stored _ _ (CW_A_fits w1 w2)). Qed.
(* NEGATIVE CONTROL R1 (the internal file WILD-COUNT.md): one slot more than the universe holds is refused at every depot *)
Lemma wild_room_R1_A : forall d, ~ YCbqGwild.wild_room ACej.Tfib_universe [] 3921 d.
Proof. intros d. apply YCbqGwild.wild_room_too_big. rewrite A_wmax. cbn [length]. lia. Qed.
(* C-TXTRACE: the tx_put realloc trace is in A's universe for ANY later words. 0x53c74 is
   cf_pc_realloc_ra0 (lib/A/CfImgA.v:50) and 0x84db0 is pi_ret_tx_realloc (lib/A/PRH_Img.v:169, PRH_Base.v:335);
   [0x53c74; 0x84db0] is the third prefix of ACej.Tfib_wild. *)
Lemma tx_trace_inU_A : forall a b ch, inU ACej.Tfib_universe (unwind_of_chain 0x53c74 ((a, 0x84db0, b) :: ch)).
Proof.
intros a b ch. apply YCbqGwild.inU_unwind_wild; [lia |].
unfold ACej.Tfib_universe, univ_of, ACej.Tfib_wild. cbn [u_wild In]. right; right; left; reflexivity.
Qed.
(* NEGATIVE CONTROL: a trace of the realloc interceptor whose second word is not a wild second word, and that is not
   fixed, is NOT in the universe *)
Lemma tx_trace_neg_A : ~ inU ACej.Tfib_universe [0x53c74; 1].
Proof.
intros [_ [Hf | [p [sfx [Hp He]]]]].
- apply mem_trace_In in Hf. vm_compute in Hf. discriminate.
- unfold ACej.Tfib_universe, univ_of, ACej.Tfib_wild in Hp. cbn [u_wild In] in Hp.
  destruct Hp as [<- | [<- | [<- | []]]]; cbn in He; discriminate.
Qed.
