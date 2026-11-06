(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset B' (fuzz_preset.asan-ubsan, ELF sha256 c90d4fa54d43160b), THE SATISFIABILITY
   WITNESSES of the room conjunct of the trace carrier P'' at image B's universe lib/Reusable/YCej.v (the trace-carrier
   form, dd7d1838e568, as at a working branch 460396d4bd13) (a Theorem Labs lane's VERIFY rule 1, ruled
   22:54Z). rule 24: no function proved. rule 24: proves no function (kind: instance facts).
   ONE IMAGE: this file Requires image B's universe and driver traces only (YCej, YF0m); image A's are
   lib/A/WildRoomInstA.v. The image-free parts (K_LLVMF, init_depot_nil, wild_room_init_K, wild_room_run_fits, cw_of,
   wild_room_cw_fix / _init / _stored) are lib/Reusable/YCbqGwild.v's.
   The start state is YG00.v init_state (lib/AU/PresetD1preB.v:260 at a working branch d60353b01f6f),
   whose depot is [] (YCbqGwild.init_depot_nil). Before the first entry call the driver stores only DRV_TRACES
   (lib/Reusable/YF0m.v), all fixed in YCej's universe (drv_fixed_B; lib/Reusable/YD2l.v's TfibB_syms does the same
   computation against the list form). CW_B w1 w2 is the cursor set: parse_items' and parse_string's frees
   ([0x53964; 0x87f34] / [0x53964; 0x885e4], the internal file UNIVERSE-PER-RUN.md section 2) followed by the word the unwinder reads (on
   B' data words: t0 + len and pj_parse's unwritten slot); the witnesses hold for every word. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YCej YF0m.
Import ListNotations.
Local Open Scope Z_scope.

(* the room YCej's universe leaves for wild traces: DEPOT_MAX - |u_fix| (YG01.v univ_of) *)
Lemma B_wmax : u_wmax YCej.Tfib_universe = 3926%nat.
Proof. vm_compute. reflexivity. Qed.
(* THE ENTRY ROOM at the start state: YCbqGwild.K_LLVMF fresh slots *)
Lemma wild_room_run_fits_B : (4 * YCbqGwild.K_LLVMF <= u_wmax YCej.Tfib_universe)%nat.
Proof. rewrite B_wmax. unfold YCbqGwild.K_LLVMF. lia. Qed.
Lemma wild_room_init_B : YCbqGwild.wild_room YCej.Tfib_universe [] YCbqGwild.K_LLVMF (st_depot init_state).
Proof. apply YCbqGwild.wild_room_init_K, YCbqGwild.wild_room_run_fits, wild_room_run_fits_B. Qed.
(* the driver's traces are fixed, so its depot before the first entry call has the same room *)
Lemma drv_fixed_B : forall t, In t YF0m.DRV_TRACES -> In t (u_fix YCej.Tfib_universe).
Proof.
intros t Ht. apply mem_trace_In.
assert (R : forallb (fun t0 => mem_trace t0 (u_fix YCej.Tfib_universe)) YF0m.DRV_TRACES = true)
  by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) R t Ht).
Qed.
Lemma wild_room_drv_B : forall d, incl d YF0m.DRV_TRACES ->
  YCbqGwild.wild_room YCej.Tfib_universe [] YCbqGwild.K_LLVMF d.
Proof.
intros d Hd. apply YCbqGwild.wild_room_fixed; [intros t Ht; exact (drv_fixed_B t (Hd t Ht)) |].
cbn [length]. exact (YCbqGwild.wild_room_run_fits _ wild_room_run_fits_B).
Qed.
(* THE CURSOR SET of a pj_parse call on B' *)
Definition CW_B (w1 w2 : Z) : list (list Z) := YCbqGwild.cw_of YCej.Tfib_wild w1 w2.
Lemma CW_B_fits : forall w1 w2, (length (CW_B w1 w2) <= u_wmax YCej.Tfib_universe)%nat.
Proof. intros w1 w2. unfold CW_B. rewrite YCbqGwild.cw_of_length, B_wmax. lia. Qed.
Lemma wild_room_cw_B : forall w1 w2 d, (forall t, In t d -> In t (u_fix YCej.Tfib_universe) \/ In t (CW_B w1 w2)) ->
  YCbqGwild.wild_room YCej.Tfib_universe (CW_B w1 w2) 0 d.
Proof. intros w1 w2 d Hd. exact (YCbqGwild.wild_room_cw_fix _ _ _ Hd (CW_B_fits w1 w2)). Qed.
(* the witnesses: at the start state, CW not stored yet; and both of CW's traces stored *)
Lemma wild_room_cw_init_B : forall w1 w2, YCbqGwild.wild_room YCej.Tfib_universe (CW_B w1 w2) 0 (st_depot init_state).
Proof. intros w1 w2. exact (YCbqGwild.wild_room_cw_init _ _ (CW_B_fits w1 w2)). Qed.
Lemma wild_room_cw_stored_B : forall w1 w2, YCbqGwild.wild_room YCej.Tfib_universe (CW_B w1 w2) 0 (CW_B w1 w2).
Proof. intros w1 w2. exact (YCbqGwild.wild_room_cw_stored _ _ (CW_B_fits w1 w2)). Qed.
(* NEGATIVE CONTROL R1 (the internal file WILD-COUNT.md): one slot more than the universe holds is refused at every depot *)
Lemma wild_room_R1_B : forall d, ~ YCbqGwild.wild_room YCej.Tfib_universe [] 3927 d.
Proof. intros d. apply YCbqGwild.wild_room_too_big. rewrite B_wmax. cbn [length]. lia. Qed.
(* C-TXTRACE: the tx_put realloc trace is in B's universe for ANY later words. 0x53d60 is
   cf_pc_realloc_ra0 (lib/AU/CfImgB.v:50) and 0x8529c is pi_ret_tx_realloc (lib/B/PRH_ImgB.v:169);
   [0x53d60; 0x8529c] is the third prefix of YCej.Tfib_wild. *)
Lemma tx_trace_inU_B : forall a b ch, inU YCej.Tfib_universe (unwind_of_chain 0x53d60 ((a, 0x8529c, b) :: ch)).
Proof.
intros a b ch. apply YCbqGwild.inU_unwind_wild; [lia |].
unfold YCej.Tfib_universe, univ_of, YCej.Tfib_wild. cbn [u_wild In]. right; right; left; reflexivity.
Qed.
(* NEGATIVE CONTROL: a trace of the realloc interceptor whose second word is not a wild second word, and that is not
   fixed, is NOT in the universe *)
Lemma tx_trace_neg_B : ~ inU YCej.Tfib_universe [0x53d60; 1].
Proof.
intros [_ [Hf | [p [sfx [Hp He]]]]].
- apply mem_trace_In in Hf. vm_compute in Hf. discriminate.
- unfold YCej.Tfib_universe, univ_of, YCej.Tfib_wild in Hp. cbn [u_wild In] in Hp.
  destruct Hp as [<- | [<- | [<- | []]]]; cbn in He; discriminate.
Qed.
