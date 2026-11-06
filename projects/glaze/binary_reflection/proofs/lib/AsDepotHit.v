(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mmM : word := Z_to_bv 64 0xc6a4a7935bd1e995.
Definition mmSEED : word := Z_to_bv 64 0x9747b28c9747b28c.
Definition mmM8 : word := Z_to_bv 64 0x35253c9ade8f4ca8.       (* [comment removed for export] *)
Definition mm_add (h k : word) : word :=
  v_mul (v_xor (v_mul (v_xor (v_srli (v_mul k mmM) 47) (v_mul k mmM)) mmM) h) mmM.
(* [comment removed for export] *)
Definition sd_h0 (sz : Z) : word := v_xor (v_mul (Z_to_bv 64 sz) mmM8) mmSEED.
Fixpoint mm_fold (h : word) (ws : list word) : word := match ws with [] => h | w :: r => mm_fold (mm_add h w) r end.
Definition sd_fin (h : word) (tag : Z) : word :=
  let x1 := mm_add h (Z_to_bv 64 tag) in
  let x2 := v_mul (v_xor (v_srli x1 47) x1) mmM in
  v_xor (v_srli x2 47) x2.
Definition sd_hashN (ws : list word) (tag : Z) : word := sd_fin (mm_fold (sd_h0 (Z.of_nat (length ws))) ws) tag.

Definition sd_bix (h : word) : Z := (bv_unsigned h mod 2 ^ 20)%Z.      (* [comment removed for export] *)

Definition sdput_words : list (option (bv 32)) :=
  [
   Some W_8ea78; None; None; Some W_8ea84; Some W_8ea88; Some W_8ea8c; Some W_8ea90; Some W_8ea94; Some W_8ea98;
   Some W_8ea9c; Some W_8eaa0; Some W_8eaa4; Some W_8eaa8; Some W_8eaac; Some W_8eab0; Some W_8eab4; Some
   W_8eab8; Some W_8eabc; Some W_8eac0; Some W_8eac4; Some W_8eac8; Some W_8eacc; Some W_8ead0; Some W_8ead4;
   Some W_8ead8; Some W_8eadc; Some W_8eae0; Some W_8eae4; Some W_8eae8; Some W_8eaec; Some W_8eaf0; Some
   W_8eaf4; None; None; Some W_8eb00; None; Some W_8eb08; None; None; None; Some W_8eb18;
   Some W_8eb1c; Some W_8eb20; Some W_8eb24; Some W_8eb28; Some W_8eb2c; Some W_8eb30; Some W_8eb34; Some
   W_8eb38; Some W_8eb3c; Some W_8eb40; Some W_8eb44; Some W_8eb48; Some W_8eb4c; Some W_8eb50; Some W_8eb54;
   Some W_8eb58; Some W_8eb5c; Some W_8eb60; Some W_8eb64; Some W_8eb68; Some W_8eb6c; Some W_8eb70; Some
   W_8eb74; Some W_8eb78; Some W_8eb7c; Some W_8eb80; Some W_8eb84; Some W_8eb88; Some W_8eb8c; Some W_8eb90;
   Some W_8eb94; Some W_8eb98; Some W_8eb9c; Some W_8eba0; Some W_8eba4; Some W_8eba8; Some W_8ebac; Some
   W_8ebb0; Some W_8ebb4; Some W_8ebb8; Some W_8ebbc; Some W_8ebc0; Some W_8ebc4; Some W_8ebc8; Some W_8ebcc;
   Some W_8ebd0; Some W_8ebd4; Some W_8ebd8; Some W_8ebdc; Some W_8ebe0; Some W_8ebe4; Some W_8ebe8; Some
   W_8ebec; Some W_8ebf0; Some W_8ebf4; Some W_8ebf8; Some W_8ebfc; Some W_8ec00; Some W_8ec04; Some W_8ec08;
   Some W_8ec0c; Some W_8ec10; Some W_8ec14; Some W_8ec18; Some W_8ec1c; Some W_8ec20; Some W_8ec24; Some
   W_8ec28; Some W_8ec2c; Some W_8ec30; Some W_8ec34; Some W_8ec38; Some W_8ec3c; Some W_8ec40; Some W_8ec44;
   Some W_8ec48; Some W_8ec4c; Some W_8ec50; Some W_8ec54; Some W_8ec58; Some W_8ec5c; Some W_8ec60; Some
   W_8ec64; Some W_8ec68; Some W_8ec6c; Some W_8ec70; Some W_8ec74; Some W_8ec78; Some W_8ec7c; Some W_8ec80;
   Some W_8ec84; Some W_8ec88; Some W_8ec8c; Some W_8ec90; Some W_8ec94; Some W_8ec98; Some W_8ec9c; Some
   W_8eca0; Some W_8eca4; Some W_8eca8; Some W_8ecac; Some W_8ecb0; Some W_8ecb4; Some W_8ecb8; Some W_8ecbc;
   Some W_8ecc0; Some W_8ecc4; Some W_8ecc8; Some W_8eccc; Some W_8ecd0; Some W_8ecd4; Some W_8ecd8; Some
   W_8ecdc; Some W_8ece0; Some W_8ece4; Some W_8ece8; Some W_8ecec; Some W_8ecf0
  ]%list.

Definition sd_clob : list reg := [10; 11; 12; 13; 14; 15; 16; 17].
Definition sd_clobx : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 10; 11; 12; 13; 14; 15; 16; 17].

(* [comment removed for export] *)
Definition sd_frame (mem : word -> option byte) (sp : word) (regs : bvmap 5 word) (ra tr a1w : word) : word -> option byte :=
  wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
    (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)))
    (at_ sp (-56)) (LE8 (getr regs 21))) (at_ sp (-64)) (LE8 (getr regs 22))) (at_ sp (-72)) (LE8 (getr regs 23)))
    (at_ sp (-80)) (LE8 (getr regs 24))) (at_ sp (-88)) (LE8 (getr regs 25)))
    (at_ sp (-104)) (LE8 tr)) (at_ sp (-96)) (LE8 a1w).

Lemma sd_frame_outside : forall mem sp regs ra tr a1w (x : word),
  (112 <= bv_unsigned sp)%Z ->
  (bv_unsigned x < bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned x)%Z ->
  sd_frame mem sp regs ra tr a1w x = mem x.
Proof using.
  intros mem sp regs ra tr a1w x Hsp Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold sd_frame in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
Qed.

Record sd_tab := SDT { st_base : word; st_depot : word; st_g_m8 : Z; st_g_seed : Z; st_g_m : Z }.
Record sd_tab_ok (segs : list Segment) (t : sd_tab) : Prop := SDTOK {
  sto_code : code_ato segs (st_base t) 0 sdput_words;
  sto_a4 : gaddr2 segs (st_base t) 4 11 11 (st_depot t);
  sto_g128 : gauipc_ld segs (st_base t) 128 156 14 10 (st_g_m t);
  sto_g132 : gauipc_ld segs (st_base t) 132 140 15 15 (st_g_m8 t);
  sto_g148 : gauipc_ld segs (st_base t) 148 152 10 16 (st_g_seed t);
  sto_depot : (bv_unsigned (st_depot t) + 0x500000 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Lemma skipn_nth_cons : forall {A} (l : list A) (i : nat) (d : A), (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof using.
  intros A l. induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply IH. lia.
Qed.
Lemma skipn_nil_len : forall {A} (l : list A) (i : nat), (length l <= i)%nat -> skipn i l = [].
Proof using. intros A l i Hi. apply skipn_all2. exact Hi. Qed.

Section DEPOT.
  Variable segs : list Segment.
  Variables base D : word.
  Variables g_m8 g_seed g_m : Z.
  Hypothesis HC : code_ato segs base 0 sdput_words.
  Hypothesis A4 : gaddr2 segs base 4 11 11 D.
  Hypothesis G128 : gauipc_ld segs base 128 156 14 10 g_m.
  Hypothesis G132 : gauipc_ld segs base 132 140 15 15 g_m8.
  Hypothesis G148 : gauipc_ld segs base 148 152 10 16 g_seed.
  Hypothesis HD : (bv_unsigned D + 0x500000 < 2 ^ 64)%Z.

  Lemma Xf2378 : fetch_word segs (at_ base 0) = Some W_8ea78.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 0 _ HC eq_refl). Qed.
  Lemma Xf2384 : fetch_word segs (at_ base 12) = Some W_8ea84.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 3 _ HC eq_refl). Qed.
  Lemma Xf2388 : fetch_word segs (at_ base 16) = Some W_8ea88.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 4 _ HC eq_refl). Qed.
  Lemma Xf238c : fetch_word segs (at_ base 20) = Some W_8ea8c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 5 _ HC eq_refl). Qed.
  Lemma Xf2390 : fetch_word segs (at_ base 24) = Some W_8ea90.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 6 _ HC eq_refl). Qed.
  Lemma Xf2394 : fetch_word segs (at_ base 28) = Some W_8ea94.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 7 _ HC eq_refl). Qed.
  Lemma Xf2398 : fetch_word segs (at_ base 32) = Some W_8ea98.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 8 _ HC eq_refl). Qed.
  Lemma Xf239c : fetch_word segs (at_ base 36) = Some W_8ea9c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 9 _ HC eq_refl). Qed.
  Lemma Xf23a0 : fetch_word segs (at_ base 40) = Some W_8eaa0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 10 _ HC eq_refl). Qed.
  Lemma Xf23a4 : fetch_word segs (at_ base 44) = Some W_8eaa4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 11 _ HC eq_refl). Qed.
  Lemma Xf23a8 : fetch_word segs (at_ base 48) = Some W_8eaa8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 12 _ HC eq_refl). Qed.
  Lemma Xf23ac : fetch_word segs (at_ base 52) = Some W_8eaac.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 13 _ HC eq_refl). Qed.
  Lemma Xf23b0 : fetch_word segs (at_ base 56) = Some W_8eab0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 14 _ HC eq_refl). Qed.
  Lemma Xf23b4 : fetch_word segs (at_ base 60) = Some W_8eab4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 15 _ HC eq_refl). Qed.
  Lemma Xf23b8 : fetch_word segs (at_ base 64) = Some W_8eab8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 16 _ HC eq_refl). Qed.
  Lemma Xf23bc : fetch_word segs (at_ base 68) = Some W_8eabc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 17 _ HC eq_refl). Qed.
  Lemma Xf23c0 : fetch_word segs (at_ base 72) = Some W_8eac0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 18 _ HC eq_refl). Qed.
  Lemma Xf23c4 : fetch_word segs (at_ base 76) = Some W_8eac4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 19 _ HC eq_refl). Qed.
  Lemma Xf23c8 : fetch_word segs (at_ base 80) = Some W_8eac8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 20 _ HC eq_refl). Qed.
  Lemma Xf23cc : fetch_word segs (at_ base 84) = Some W_8eacc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 21 _ HC eq_refl). Qed.
  Lemma Xf23d0 : fetch_word segs (at_ base 88) = Some W_8ead0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 22 _ HC eq_refl). Qed.
  Lemma Xf23d4 : fetch_word segs (at_ base 92) = Some W_8ead4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 23 _ HC eq_refl). Qed.
  Lemma Xf23d8 : fetch_word segs (at_ base 96) = Some W_8ead8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 24 _ HC eq_refl). Qed.
  Lemma Xf23e0 : fetch_word segs (at_ base 104) = Some W_8eae0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 26 _ HC eq_refl). Qed.
  Lemma Xf23e4 : fetch_word segs (at_ base 108) = Some W_8eae4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 27 _ HC eq_refl). Qed.
  Lemma Xf23e8 : fetch_word segs (at_ base 112) = Some W_8eae8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 28 _ HC eq_refl). Qed.
  Lemma Xf23ec : fetch_word segs (at_ base 116) = Some W_8eaec.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 29 _ HC eq_refl). Qed.
  Lemma Xf23f0 : fetch_word segs (at_ base 120) = Some W_8eaf0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 30 _ HC eq_refl). Qed.
  Lemma Xf23f4 : fetch_word segs (at_ base 124) = Some W_8eaf4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 31 _ HC eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Xf2400 : fetch_word segs (at_ base 136) = Some W_8eb00.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 34 _ HC eq_refl). Qed.
  Lemma Xf2408 : fetch_word segs (at_ base 144) = Some W_8eb08.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 36 _ HC eq_refl). Qed.
  Lemma Xf2418 : fetch_word segs (at_ base 160) = Some W_8eb18.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 40 _ HC eq_refl). Qed.
  Lemma Xf241c : fetch_word segs (at_ base 164) = Some W_8eb1c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 41 _ HC eq_refl). Qed.
  Lemma Xf2420 : fetch_word segs (at_ base 168) = Some W_8eb20.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 42 _ HC eq_refl). Qed.
  Lemma Xf2424 : fetch_word segs (at_ base 172) = Some W_8eb24.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 43 _ HC eq_refl). Qed.
  Lemma Xf2428 : fetch_word segs (at_ base 176) = Some W_8eb28.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 44 _ HC eq_refl). Qed.
  Lemma Xf242c : fetch_word segs (at_ base 180) = Some W_8eb2c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 45 _ HC eq_refl). Qed.
  Lemma Xf2430 : fetch_word segs (at_ base 184) = Some W_8eb30.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 46 _ HC eq_refl). Qed.
  Lemma Xf2434 : fetch_word segs (at_ base 188) = Some W_8eb34.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 47 _ HC eq_refl). Qed.
  Lemma Xf2438 : fetch_word segs (at_ base 192) = Some W_8eb38.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 48 _ HC eq_refl). Qed.
  Lemma Xf243c : fetch_word segs (at_ base 196) = Some W_8eb3c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 49 _ HC eq_refl). Qed.
  Lemma Xf2440 : fetch_word segs (at_ base 200) = Some W_8eb40.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 50 _ HC eq_refl). Qed.
  Lemma Xf2444 : fetch_word segs (at_ base 204) = Some W_8eb44.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 51 _ HC eq_refl). Qed.
  Lemma Xf2448 : fetch_word segs (at_ base 208) = Some W_8eb48.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 52 _ HC eq_refl). Qed.
  Lemma Xf244c : fetch_word segs (at_ base 212) = Some W_8eb4c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 53 _ HC eq_refl). Qed.
  Lemma Xf2450 : fetch_word segs (at_ base 216) = Some W_8eb50.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 54 _ HC eq_refl). Qed.
  Lemma Xf2454 : fetch_word segs (at_ base 220) = Some W_8eb54.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 55 _ HC eq_refl). Qed.
  Lemma Xf2458 : fetch_word segs (at_ base 224) = Some W_8eb58.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 56 _ HC eq_refl). Qed.
  Lemma Xf245c : fetch_word segs (at_ base 228) = Some W_8eb5c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 57 _ HC eq_refl). Qed.
  Lemma Xf2460 : fetch_word segs (at_ base 232) = Some W_8eb60.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 58 _ HC eq_refl). Qed.
  Lemma Xf2464 : fetch_word segs (at_ base 236) = Some W_8eb64.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 59 _ HC eq_refl). Qed.
  Lemma Xf2468 : fetch_word segs (at_ base 240) = Some W_8eb68.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 60 _ HC eq_refl). Qed.
  Lemma Xf246c : fetch_word segs (at_ base 244) = Some W_8eb6c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 61 _ HC eq_refl). Qed.
  Lemma Xf2470 : fetch_word segs (at_ base 248) = Some W_8eb70.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 62 _ HC eq_refl). Qed.
  Lemma Xf2474 : fetch_word segs (at_ base 252) = Some W_8eb74.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 63 _ HC eq_refl). Qed.
  Lemma Xf2478 : fetch_word segs (at_ base 256) = Some W_8eb78.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 64 _ HC eq_refl). Qed.
  Lemma Xf247c : fetch_word segs (at_ base 260) = Some W_8eb7c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 65 _ HC eq_refl). Qed.
  Lemma Xf2480 : fetch_word segs (at_ base 264) = Some W_8eb80.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 66 _ HC eq_refl). Qed.
  Lemma Xf2484 : fetch_word segs (at_ base 268) = Some W_8eb84.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 67 _ HC eq_refl). Qed.
  Lemma Xf2488 : fetch_word segs (at_ base 272) = Some W_8eb88.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 68 _ HC eq_refl). Qed.
  Lemma Xf248c : fetch_word segs (at_ base 276) = Some W_8eb8c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 69 _ HC eq_refl). Qed.
  Lemma Xf2490 : fetch_word segs (at_ base 280) = Some W_8eb90.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 70 _ HC eq_refl). Qed.
  Lemma Xf2494 : fetch_word segs (at_ base 284) = Some W_8eb94.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 71 _ HC eq_refl). Qed.
  Lemma Xf2498 : fetch_word segs (at_ base 288) = Some W_8eb98.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 72 _ HC eq_refl). Qed.
  Lemma Xf249c : fetch_word segs (at_ base 292) = Some W_8eb9c.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 73 _ HC eq_refl). Qed.
  Lemma Xf24a0 : fetch_word segs (at_ base 296) = Some W_8eba0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 74 _ HC eq_refl). Qed.
  Lemma Xf24a4 : fetch_word segs (at_ base 300) = Some W_8eba4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 75 _ HC eq_refl). Qed.
  Lemma Xf24a8 : fetch_word segs (at_ base 304) = Some W_8eba8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 76 _ HC eq_refl). Qed.
  Lemma Xf24ac : fetch_word segs (at_ base 308) = Some W_8ebac.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 77 _ HC eq_refl). Qed.
  Lemma Xf24b0 : fetch_word segs (at_ base 312) = Some W_8ebb0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 78 _ HC eq_refl). Qed.
  Lemma Xf24b4 : fetch_word segs (at_ base 316) = Some W_8ebb4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 79 _ HC eq_refl). Qed.
  Lemma Xf24b8 : fetch_word segs (at_ base 320) = Some W_8ebb8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 80 _ HC eq_refl). Qed.
  Lemma Xf24bc : fetch_word segs (at_ base 324) = Some W_8ebbc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 81 _ HC eq_refl). Qed.
  Lemma Xf24c0 : fetch_word segs (at_ base 328) = Some W_8ebc0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 82 _ HC eq_refl). Qed.
  Lemma Xf24c4 : fetch_word segs (at_ base 332) = Some W_8ebc4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 83 _ HC eq_refl). Qed.
  Lemma Xf24c8 : fetch_word segs (at_ base 336) = Some W_8ebc8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 84 _ HC eq_refl). Qed.
  Lemma Xf24cc : fetch_word segs (at_ base 340) = Some W_8ebcc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 85 _ HC eq_refl). Qed.
  Lemma Xf24d0 : fetch_word segs (at_ base 344) = Some W_8ebd0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 86 _ HC eq_refl). Qed.
  Lemma Xf24d4 : fetch_word segs (at_ base 348) = Some W_8ebd4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 87 _ HC eq_refl). Qed.
  Lemma Xf24d8 : fetch_word segs (at_ base 352) = Some W_8ebd8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 88 _ HC eq_refl). Qed.
  Lemma Xf24dc : fetch_word segs (at_ base 356) = Some W_8ebdc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 89 _ HC eq_refl). Qed.
  Lemma Xf24e0 : fetch_word segs (at_ base 360) = Some W_8ebe0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 90 _ HC eq_refl). Qed.
  Lemma Xf24e4 : fetch_word segs (at_ base 364) = Some W_8ebe4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 91 _ HC eq_refl). Qed.
  Lemma Xf24e8 : fetch_word segs (at_ base 368) = Some W_8ebe8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 92 _ HC eq_refl). Qed.
  Lemma Xf24ec : fetch_word segs (at_ base 372) = Some W_8ebec.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 93 _ HC eq_refl). Qed.
  Lemma Xf24f0 : fetch_word segs (at_ base 376) = Some W_8ebf0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 94 _ HC eq_refl). Qed.
  Lemma Xf24f4 : fetch_word segs (at_ base 380) = Some W_8ebf4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 95 _ HC eq_refl). Qed.
  Lemma Xf25bc : fetch_word segs (at_ base 580) = Some W_8ecbc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 145 _ HC eq_refl). Qed.
  Lemma Xf25c0 : fetch_word segs (at_ base 584) = Some W_8ecc0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 146 _ HC eq_refl). Qed.
  Lemma Xf25c4 : fetch_word segs (at_ base 588) = Some W_8ecc4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 147 _ HC eq_refl). Qed.
  Lemma Xf25c8 : fetch_word segs (at_ base 592) = Some W_8ecc8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 148 _ HC eq_refl). Qed.
  Lemma Xf25cc : fetch_word segs (at_ base 596) = Some W_8eccc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 149 _ HC eq_refl). Qed.
  Lemma Xf25d0 : fetch_word segs (at_ base 600) = Some W_8ecd0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 150 _ HC eq_refl). Qed.
  Lemma Xf25d4 : fetch_word segs (at_ base 604) = Some W_8ecd4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 151 _ HC eq_refl). Qed.
  Lemma Xf25d8 : fetch_word segs (at_ base 608) = Some W_8ecd8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 152 _ HC eq_refl). Qed.
  Lemma Xf25dc : fetch_word segs (at_ base 612) = Some W_8ecdc.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 153 _ HC eq_refl). Qed.
  Lemma Xf25e0 : fetch_word segs (at_ base 616) = Some W_8ece0.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 154 _ HC eq_refl). Qed.
  Lemma Xf25e4 : fetch_word segs (at_ base 620) = Some W_8ece4.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 155 _ HC eq_refl). Qed.
  Lemma Xf25e8 : fetch_word segs (at_ base 624) = Some W_8ece8.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 156 _ HC eq_refl). Qed.
  Lemma Xf25ec : fetch_word segs (at_ base 628) = Some W_8ecec.   (* [comment removed for export] *)
  Proof using HC. exact (code_ato_get segs base 0 sdput_words 157 _ HC eq_refl). Qed.

  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables tr sp ra : word.
  Variable ws : list word.                 (* [comment removed for export] *)
  Variables sz tag : Z.                     (* [comment removed for export] *)
  Variable NIDS : Z.                        (* [comment removed for export] *)
  Variables (tabf : Z -> Z) (blkf : Z -> word) (hashf : Z -> word) (linkf : Z -> Z).
  #[local] Abbreviation U := bv_unsigned.
  #[local] Abbreviation a1w := (Z_to_bv 64 (sz + tag * 2 ^ 32)).
  #[local] Abbreviation HSH := (sd_hashN ws tag).
  (* [comment removed for export] *)
  Definition nd (id : Z) : word := at_ (blkf (id / 2 ^ 16)) (16 * (id mod 2 ^ 16)).

  Hypothesis Hsz : Z.of_nat (length ws) = sz /\ (1 <= sz < 2 ^ 31)%Z.
  Hypothesis Htag : (0 <= tag < 2 ^ 32)%Z.
  Hypothesis Rws : forall i, (i < length ws)%nat -> rdn segs mem (at_ tr (8 * Z.of_nat i)) 8 = Some (LE8 (nth i ws (Z_to_bv 64 0))).
  Hypothesis Rm8 : rdn segs mem (Z_to_bv 64 g_m8) 8 = Some (LE8 mmM8).
  Hypothesis Rseed : rdn segs mem (Z_to_bv 64 g_seed) 8 = Some (LE8 mmSEED).
  Hypothesis Rm : rdn segs mem (Z_to_bv 64 g_m) 8 = Some (LE8 mmM).
  Hypothesis Hnids : (0 <= NIDS < 2 ^ 31 - 1)%Z.
  Hypothesis Rtab : forall b, (0 <= b < 2 ^ 20)%Z -> rdn segs mem (Z_to_bv 64 (U D + 4 * b)) 4 = Some (LE4 (tabf b)) /\ (0 <= tabf b <= NIDS)%Z.
  Hypothesis Rmap : forall i, (0 <= i <= NIDS / 2 ^ 16)%Z ->
    rdn segs mem (Z_to_bv 64 (U D + 0x400010 + 8 * i)) 8 = Some (LE8 (blkf i)) /\ U (blkf i) <> 0%Z /\ (U (blkf i) + 2 ^ 20 <= 2 ^ 64)%Z.
  Hypothesis Rnode : forall id, (1 <= id <= NIDS)%Z ->
    rdn segs mem (nd id) 8 = Some (LE8 (hashf id)) /\ rdn segs mem (at_ (nd id) 8) 4 = Some (LE4 (linkf id)) /\ (0 <= linkf id < id)%Z.
  (* [comment removed for export] *)
  Hypothesis Hsp : (2 ^ 32 + 112 <= U sp)%Z /\ (U sp < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-112)) 112 = true.
  Hypothesis Htr : (U tr + 8 * sz <= U sp - 112 \/ U sp <= U tr)%Z /\ (0 < U tr)%Z /\ (U tr + 8 * sz < 2 ^ 64)%Z.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= 2 ^ 32)%Z [g_m8; g_seed; g_m].
  Hypothesis HD32 : (U D + 0x500000 <= 2 ^ 32)%Z.
  Hypothesis Hblk : forall i, (0 <= i <= NIDS / 2 ^ 16)%Z -> (U (blkf i) + 2 ^ 20 <= U sp - 112 \/ U sp <= U (blkf i))%Z.
  Hypothesis Hret : ret_ok ra.

  #[local] Abbreviation CL := (fun r => In r sd_clob).
  #[local] Abbreviation CLX := (fun r => In r sd_clobx).

  Lemma X0' : fetch_word segs base = Some W_8ea78.
  Proof using HC. rewrite <- (at_0 base). exact Xf2378. Qed.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.

  Lemma bix_range : forall h : word, (0 <= sd_bix h < 2 ^ 20)%Z.
  Proof using. intros h. (lazymatch goal with |- ?G => let G' := eval unfold sd_bix in G in change_no_check G' end). apply Z.mod_pos_bound. lia. Qed.
  Lemma id16 : forall id, (0 <= id <= NIDS)%Z -> (0 <= id / 2 ^ 16 <= NIDS / 2 ^ 16)%Z /\ (0 <= id mod 2 ^ 16 < 2 ^ 16)%Z /\ (id / 2 ^ 16 < 2 ^ 15)%Z.
  Proof using Hnids ws.
    intros id Hid. split; [split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia] |].
    split; [apply Z.mod_pos_bound; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma Ua1w : U a1w = (sz + tag * 2 ^ 32)%Z.
  Proof using Htag Hsz ws. unorm. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma bix_shift : forall h : word, v_srli (v_slli h 44) 42 = Z_to_bv 64 (4 * sd_bix h).
  Proof using ws.
    intros h. pose proof (u64_range h). (lazymatch goal with |- ?G => let G' := eval unfold v_srli, v_slli, sd_bix in G in change_no_check G' end). f_equal.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 44 * 2 ^ 20)%Z.
    rewrite Z.mul_comm. rewrite Z.mul_mod_distr_l by lia.
    replace (2 ^ 44)%Z with (2 ^ 42 * 4)%Z by reflexivity.
    rewrite <- Z.mul_assoc, (Z.mul_comm (2 ^ 42)), Z.div_mul by lia. lia.
  Qed.
  Lemma land_ones_small : forall a k, (0 < k)%Z -> (0 <= a < 2 ^ k)%Z -> Z.land a (Z.ones k) = a.
  Proof using ws. intros a k Hk Ha. rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
  Lemma v_and_bw31 : forall BW, (0 <= BW < 2 ^ 31)%Z -> v_and (Z_to_bv 64 BW) (Z_to_bv 64 2147483647) = Z_to_bv 64 BW.
  Proof using ws. intros BW HBW. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). unorm. change 2147483647%Z with (Z.ones 31). rewrite land_ones_small by lia. reflexivity. Qed.
  Lemma v_srliw_bw : forall BW, (0 <= BW < 2 ^ 31)%Z -> v_srliw (Z_to_bv 64 BW) 16 = Z_to_bv 64 (BW / 2 ^ 16).
  Proof using ws.
    intros BW HBW. assert (0 <= BW / 2 ^ 16 < 2 ^ 15)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    (lazymatch goal with |- ?G => let G' := eval unfold v_srliw in G in change_no_check G' end). f_equal. unorm. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_swrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32)%Z.
    change (bv_half_modulus 32) with (2 ^ 31)%Z.
    rewrite (Z.mod_small BW) by lia. rewrite Z.shiftr_div_pow2 by lia. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32)%Z.
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma v_and_bw16 : forall BW (x : word), (0 <= BW < 2 ^ 31)%Z -> bv_unsigned x = BW -> v_and x (Z_to_bv 64 65535) = Z_to_bv 64 (BW mod 2 ^ 16).
  Proof using. intros BW x HBW Hx. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite Hx. unorm. change 65535%Z with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.


  Section WithRegs.
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = tr.
  Hypothesis H11 : getr regs 11 = a1w.

  Definition SM1 : word -> option byte := sd_frame mem sp regs ra tr a1w.

  Lemma SM1_out : forall x : word, (U x < U sp - 112 \/ U sp <= U x)%Z -> SM1 x = mem x.
  Proof using Hsp ws. intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold SM1 in G in change_no_check G' end). apply sd_frame_outside; [lia | exact Hx]. Qed.

  (* [comment removed for export] *)
  Lemma rd_o2 : forall (a : word) k bs,
    (U a + Z.of_nat k <= U sp - 112 \/ U sp <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs -> rdn segs SM1 a k = Some bs.
  Proof using Hsp ws.
    intros a k bs Ha Hnw Hr. rewrite <- Hr. apply rdn_ext; [lia|].
    intros x Hx. apply SM1_out. lia.
  Qed.

  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-112)) _ 112);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac addr_n := gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; rewrite ?at_addi; zlit_at;
                 try (progress ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end)); unorm).
  Ltac rd_close Hr :=
    apply rd_o2;
    [ rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | first [ exact Hr | rewrite <- Hr; f_equal; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ] ].
  Ltac cld F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D | addr_n; rd_close Hr | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac clw F D z Hr :=
    chain_step; [reflexivity
      | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 z)) (v := Z_to_bv 64 z);
        [exact F | reflexivity | exact D | addr_n; rd_close Hr | apply bytes4_small; lia]
      | step_simpl]; rewrite (v_lw_small z) by lia; vn.

  (* [comment removed for export] *)
  Lemma sextw_sz : v_addiw a1w 0 = Z_to_bv 64 sz.
  Proof using Htag Hsz ws.
    (lazymatch goal with |- ?G => let G' := eval unfold v_addiw in G in change_no_check G' end). f_equal. rewrite Ua1w. rewrite Z.add_0_r. (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end).
    change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
    rewrite <- (Z.add_assoc), (Z.add_comm (tag * 2 ^ 32)), Z.add_assoc, Z.mod_add by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma srli32_tag : v_srli a1w 32 = Z_to_bv 64 tag.
  Proof using Htag Hsz ws. (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end). f_equal. rewrite Ua1w, Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. Qed.
  Lemma and32_sz : v_and a1w (Z_to_bv 64 4294967295) = Z_to_bv 64 sz.
  Proof using Htag Hsz ws.
    (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). f_equal. rewrite Ua1w. unorm. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma D1 :
    exists r,
      msteps segs (mkst regs base mem rom) (mkst r (at_ base 160) SM1 rom)
      /\ getr r 2 = at_ sp (-112) /\ getr r 9 = D /\ getr r 11 = tr /\ getr r 12 = Z_to_bv 64 sz /\ getr r 13 = Z_to_bv 64 tag
      /\ getr r 15 = mmM8 /\ getr r 16 = mmSEED /\ getr r 10 = mmM /\ getr r 8 = Z_to_bv 64 0
      /\ regs_agree CLX regs r.
  Proof using H11 H10 H2 H1 Hcells Htr Hstk Hsp Rm Rseed Rm8 Htag Hsz ws G148 G132 G128 A4 HC g_m g_seed g_m8.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tr) as Htrr. cells_split. destruct Hsz as [Hlen Hsz'].
    destruct A4 as [xa GA]. destruct G128 as [x1 [GA1 GL1]]. destruct G132 as [x2 [GA2 GL2]]. destruct G148 as [x3 [GA3 GL3]].
    wd_eexists. split.
    - an X0' D_8ea78.                                    (* [comment removed for export] *)
      eapply msteps_trans; [apply GA|]; zlit_at. rewrite regupd_regupd_same.   (* [comment removed for export] *)
      an Xf2384 D_8ea84.                                 (* [comment removed for export] *)
      an Xf2388 D_8ea88.                                 (* [comment removed for export] *)
      an Xf238c D_8ea8c.                                 (* [comment removed for export] *)
      an Xf2390 D_8ea90.                                 (* [comment removed for export] *)
      an Xf2394 D_8ea94.                                 (* [comment removed for export] *)
      an Xf2398 D_8ea98.                                 (* [comment removed for export] *)
      fsd Xf239c D_8ea9c (at_ sp (-8)).
      fsd Xf23a0 D_8eaa0 (at_ sp (-16)).
      fsd Xf23a4 D_8eaa4 (at_ sp (-24)).
      fsd Xf23a8 D_8eaa8 (at_ sp (-32)).
      fsd Xf23ac D_8eaac (at_ sp (-40)).
      fsd Xf23b0 D_8eab0 (at_ sp (-48)).
      fsd Xf23b4 D_8eab4 (at_ sp (-56)).
      fsd Xf23b8 D_8eab8 (at_ sp (-64)).
      fsd Xf23bc D_8eabc (at_ sp (-72)).
      fsd Xf23c0 D_8eac0 (at_ sp (-80)).
      fsd Xf23c4 D_8eac4 (at_ sp (-88)).
      an Xf23c8 D_8eac8.                                 (* [comment removed for export] *)
      an Xf23cc D_8eacc.                                 (* [comment removed for export] *)
      fsd Xf23d0 D_8ead0 (at_ sp (-104)).                (* [comment removed for export] *)
      fsd Xf23d4 D_8ead4 (at_ sp (-96)).                 (* [comment removed for export] *)
      change (wbytes _ _ _) with SM1.
      ab_tk Xf23d8 D_8ead8 ltac:(condz).               (* [comment removed for export] *)
      av Xf23e0 D_8eae0 (Z_to_bv 64 sz) ltac:(apply sextw_sz).   (* [comment removed for export] *)
      an Xf23e4 D_8eae4.                                 (* [comment removed for export] *)
      ab_ft Xf23e8 D_8eae8 ltac:(condz).               (* [comment removed for export] *)
      ab_ft Xf23ec D_8eaec ltac:(condz).               (* [comment removed for export] *)
      av Xf23f0 D_8eaf0 (Z_to_bv 64 tag) ltac:(apply srli32_tag).   (* [comment removed for export] *)
      an Xf23f4 D_8eaf4.                                 (* [comment removed for export] *)
      eapply msteps_trans; [apply GA1|]; zlit_at.        (* [comment removed for export] *)
      eapply msteps_trans; [apply GA2|]; zlit_at.        (* [comment removed for export] *)
      an Xf2400 D_8eb00.                                 (* [comment removed for export] *)
      eapply msteps_trans; [ eapply GL2; [gres; reflexivity | apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | exact Rm8]] | ]; zlit_at.  (* [comment removed for export] *)
      an Xf2408 D_8eb08.                                 (* [comment removed for export] *)
      first [ rewrite and32_sz
            | match goal with |- context [v_and a1w ?m] => replace (v_and a1w m) with (Z_to_bv 64 sz) by (symmetry; etransitivity; [|apply and32_sz]; f_equal; apply bv_eq; reflexivity) end ].
      eapply msteps_trans; [apply GA3|]; zlit_at.        (* [comment removed for export] *)
      eapply msteps_trans; [ eapply GL3; [gres; reflexivity | apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | exact Rseed]] | ]; zlit_at.  (* [comment removed for export] *)
      eapply msteps_trans; [ eapply GL1; [gres; reflexivity | apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | exact Rm]] | ]; zlit_at.      (* [comment removed for export] *)
      wd_refl.
    - post; rewrite ?at_0; try reflexivity. (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  #[local] Abbreviation SM := SM1.
  Ltac cld2 F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D | addr_n; rewrite ?at_add_0_r, ?Z.add_0_r; Hr | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac clw2 F D z Hr :=
    chain_step; [reflexivity
      | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 z)) (v := Z_to_bv 64 z);
        [exact F | reflexivity | exact D | addr_n; rewrite ?at_add_0_r, ?Z.add_0_r; Hr | apply bytes4_small; lia]
      | step_simpl]; rewrite (v_lw_small z) by lia; vn.

  (* [comment removed for export] *)
  Lemma D2loop : forall (k : nat) r0 (i : nat) (h : word),
    (i + S k = length ws)%nat ->
    getr r0 11 = at_ tr (8 * Z.of_nat i) -> getr r0 14 = at_ tr (8 * sz) -> getr r0 12 = h -> getr r0 10 = mmM ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 176) SM rom) (mkst r (at_ base 212) SM rom)
      /\ getr r 12 = mm_fold h (skipn i ws) /\ getr r 11 = at_ tr (8 * sz) /\ getr r 10 = mmM
      /\ (forall x : reg, In x [2; 8; 9; 13] -> getr r x = getr r0 x)
      /\ regs_agree CLX regs r.
  Proof using Htr Hsp Rws Hsz HC.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tr) as Htrr. destruct Hsz as [Hlen Hsz'].
    induction k as [|k IH]; intros r0 i h Hi R11 R14 R12 R10 AG0.
    - (* [comment removed for export] *)
      assert (Hw : rdn segs SM (at_ tr (8 * Z.of_nat i)) 8 = Some (LE8 (nth i ws (Z_to_bv 64 0)))).
      { apply rd_o2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | apply Rws; lia]. }
      wd_eexists. split.
      + cld2 Xf2428 D_8eb28 (nth i ws (Z_to_bv 64 0)) ltac:(exact Hw).   (* [comment removed for export] *)
        an Xf242c D_8eb2c.                               (* [comment removed for export] *)
        an Xf2430 D_8eb30. an Xf2434 D_8eb34. an Xf2438 D_8eb38. an Xf243c D_8eb3c. an Xf2440 D_8eb40. an Xf2444 D_8eb44.
        ab_ft Xf2448 D_8eb48 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ]).   (* [comment removed for export] *)
        wd_refl.
      + post.
        * rewrite (skipn_nth_cons ws i (Z_to_bv 64 0)) by lia. rewrite skipn_nil_len by lia. reflexivity.
        * intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx.
        * (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end). ra_chain.
    - assert (Hw : rdn segs SM (at_ tr (8 * Z.of_nat i)) 8 = Some (LE8 (nth i ws (Z_to_bv 64 0)))).
      { apply rd_o2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | apply Rws; lia]. }
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 176) SM rom)
               (fun r => getr r 11 = at_ tr (8 * Z.of_nat (S i)) /\ getr r 14 = at_ tr (8 * sz) /\ getr r 12 = mm_add h (nth i ws (Z_to_bv 64 0)) /\ getr r 10 = mmM
                         /\ (forall x : reg, In x [2; 8; 9; 13] -> getr r x = getr r0 x) /\ regs_agree CLX regs r)).
      + wd_eexists. split.
        * cld2 Xf2428 D_8eb28 (nth i ws (Z_to_bv 64 0)) ltac:(exact Hw).
          an Xf242c D_8eb2c.
          an Xf2430 D_8eb30. an Xf2434 D_8eb34. an Xf2438 D_8eb38. an Xf243c D_8eb3c. an Xf2440 D_8eb40. an Xf2444 D_8eb44.
          ab_tk Xf2448 D_8eb48 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ]).   (* [comment removed for export] *)
          wd_refl.
        * post.
          all: lazymatch goal with
               | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
               | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
               | |- _ => rewrite ?at_addi; f_equal; lia
               end.
      + cbv beta. intros r1 (Q11 & Q14 & Q12 & Q10 & QK & QAG).
        destruct (IH r1 (S i) _ ltac:(lia) Q11 Q14 Q12 Q10 QAG) as (r2 & RUN & P12 & P11 & P10 & PK & PAG).
        exists r2. split; [exact RUN|]. split; [| split; [exact P11 | split; [exact P10 | split; [| exact PAG]]]].
        * rewrite P12. rewrite (skipn_nth_cons ws i (Z_to_bv 64 0)) by lia. reflexivity.
        * intros x Hx. rewrite (PK x Hx). apply QK. exact Hx.
  Qed.

  #[local] Abbreviation BIX := (sd_bix HSH).
  #[local] Abbreviation MAP1 := (Z_to_bv 64 (U D + 4194320)).

  (* [comment removed for export] *)
  Lemma D2 : forall r0,
    getr r0 9 = D -> getr r0 11 = tr -> getr r0 12 = Z_to_bv 64 sz -> getr r0 13 = Z_to_bv 64 tag ->
    getr r0 15 = mmM8 -> getr r0 16 = mmSEED -> getr r0 10 = mmM ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 160) SM rom) (mkst r (at_ base 320) SM rom)
      /\ getr r 11 = Z_to_bv 64 (tabf BIX) /\ getr r 19 = HSH /\ getr r 24 = MAP1 /\ getr r 22 = Z_to_bv 64 65535
      /\ getr r 18 = Z_to_bv 64 (U D + 4 * BIX) /\ getr r 25 = Z_to_bv 64 (tabf BIX) /\ getr r 23 = Z_to_bv 64 2147483647
      /\ getr r 20 = Z_to_bv 64 (U D + 4194312) /\ getr r 8 = getr r0 8
      /\ (forall x : reg, In x [2; 9] -> getr r x = getr r0 x)
      /\ regs_agree CLX regs r.
  Proof using HC HD32 Hcells Hnids Hsp Hsz Htag Htr Rtab Rws.
    intros r0 R9 R11 R12 R13 R15 R16 R10 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tr) as Htrr. pose proof (u64_range D) as HDr. pose proof (bix_range HSH) as Hbix.
    destruct Hsz as [Hlen Hsz']. destruct (Rtab BIX Hbix) as [Rbucket Hbw].
    cells_split.
    (* [comment removed for export] *)
    assert (W1 : exists r1, msteps segs (mkst r0 (at_ base 160) SM rom) (mkst r1 (at_ base 176) SM rom)
                 /\ getr r1 11 = at_ tr (8 * Z.of_nat 0) /\ getr r1 14 = at_ tr (8 * sz) /\ getr r1 12 = sd_h0 sz /\ getr r1 10 = mmM
                 /\ getr r1 13 = Z_to_bv 64 tag /\ getr r1 8 = getr r0 8 /\ (forall x : reg, In x [2; 9] -> getr r1 x = getr r0 x) /\ regs_agree CLX regs r1).
    { wd_eexists. split.
      { an Xf2418 D_8eb18.                                (* [comment removed for export] *)
        av Xf241c D_8eb1c (Z_to_bv 64 (8 * sz)) ltac:(rewrite v_slli_mul by lia; unorm; f_equal; lia).   (* [comment removed for export] *)
        an Xf2420 D_8eb20.                                (* [comment removed for export] *)
        av Xf2424 D_8eb24 (at_ tr (8 * sz)) ltac:(apply v_add_at; lia).   (* [comment removed for export] *)
        wd_refl. }
      post. all: try (rewrite Z.mul_0_r, at_0; reflexivity).
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => try reflexivity
           end. }
    destruct W1 as (r1 & RUN1 & A11 & A14 & A12 & A10 & A13 & A8 & AK & AG1).
    destruct (D2loop (length ws - 1) r1 0 (sd_h0 sz) ltac:(lia) A11 A14 A12 A10 AG1) as (r2 & RUN2 & B12 & B11 & B10 & BK & AG2).
    cbn [skipn] in B12.
    assert (B13 : getr r2 13 = Z_to_bv 64 tag) by (rewrite (BK 13) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A13).
    assert (B9 : getr r2 9 = D) by (rewrite (BK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite (AK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact R9).
    (* [comment removed for export] *)
    assert (EH : sd_fin (mm_fold (sd_h0 sz) ws) tag = HSH) by ((lazymatch goal with |- ?G => let G' := eval unfold sd_hashN in G in change_no_check G' end); rewrite Hlen; reflexivity).
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 212) SM rom) (fun r => r = r2)); [exists r2; split; [|reflexivity]; eapply msteps_trans; [exact RUN1 | exact RUN2] |].
    intros r2' ->.
    wd_eexists. split.
    - an Xf244c D_8eb4c. an Xf2450 D_8eb50.           (* [comment removed for export] *)
      an Xf2454 D_8eb54.                                 (* [comment removed for export] *)
      an Xf2458 D_8eb58.                                 (* [comment removed for export] *)
      an Xf245c D_8eb5c. an Xf2460 D_8eb60.           (* [comment removed for export] *)
      an Xf2464 D_8eb64. an Xf2468 D_8eb68. an Xf246c D_8eb6c.   (* [comment removed for export] *)
      an Xf2470 D_8eb70. an Xf2474 D_8eb74.           (* [comment removed for export] *)
      an Xf2478 D_8eb78. an Xf247c D_8eb7c. an Xf2480 D_8eb80.   (* [comment removed for export] *)
      an Xf2484 D_8eb84. an Xf2488 D_8eb88.           (* [comment removed for export] *)
      match goal with |- context [regupd _ 19 ?hv] => replace hv with HSH by (rewrite <- EH; reflexivity) end.
      an Xf248c D_8eb8c.                                 (* [comment removed for export] *)
      av Xf2490 D_8eb90 (Z_to_bv 64 (4 * BIX)) ltac:(apply bix_shift).   (* [comment removed for export] *)
      av Xf2494 D_8eb94 (Z_to_bv 64 (U D + 4 * BIX)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      clw Xf2498 D_8eb98 (tabf BIX) Rbucket.            (* [comment removed for export] *)
      an Xf249c D_8eb9c.                                 (* [comment removed for export] *)
      av Xf24a0 D_8eba0 (Z_to_bv 64 (U D + 4194320)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); imm_norm; unorm; reflexivity).   (* [comment removed for export] *)
      afence Xf24a4 D_8eba4.                             (* [comment removed for export] *)
      an Xf24a8 D_8eba8. rewrite v_and_bw31 by lia.       (* [comment removed for export] *)
      an Xf24ac D_8ebac.                                 (* [comment removed for export] *)
      av Xf24b0 D_8ebb0 (Z_to_bv 64 (U D + 4194312)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); imm_norm; unorm; reflexivity).   (* [comment removed for export] *)
      an Xf24b4 D_8ebb4.                                 (* [comment removed for export] *)
      wd_refl.
    - post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; rewrite (BK _) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); apply AK; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]|]); destruct Hx
           | |- _ => idtac
           end.
      + rewrite (BK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]). exact A8.
  Qed.

  (* [comment removed for export] *)
  Lemma rdS : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
               (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24); (-88, getr regs 25)]%Z ->
    rdn segs SM (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp ws.
    intros k v Hin. pose proof (u64_range sp).
    (lazymatch goal with |- ?G => let G' := eval unfold SM1, sd_frame in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma D3 : forall r0,
    getr r0 2 = at_ sp (-112) -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 580) SM rom) (mkst r ra SM rom)
      /\ getr r 10 = getr r0 10 /\ regs_agree CL regs r.
  Proof using H1 H10 H11 H2 HC Hnids Hret Hsp Hsz Htag Htr.
    intros r0 R2 AG0. pose proof (u64_range sp) as Hspr.
    Ltac fldM F D vv :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rdS; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - fldM Xf25bc D_8ecbc ra.
      fldM Xf25c0 D_8ecc0 (getr regs 8).
      fldM Xf25c4 D_8ecc4 (getr regs 9).
      fldM Xf25c8 D_8ecc8 (getr regs 18).
      fldM Xf25cc D_8eccc (getr regs 19).
      fldM Xf25d0 D_8ecd0 (getr regs 20).
      fldM Xf25d4 D_8ecd4 (getr regs 21).
      fldM Xf25d8 D_8ecd8 (getr regs 22).
      fldM Xf25dc D_8ecdc (getr regs 23).
      fldM Xf25e0 D_8ece0 (getr regs 24).
      fldM Xf25e4 D_8ece4 (getr regs 25).
      an Xf25e8 D_8ece8.                                 (* [comment removed for export] *)
      aret Xf25ec D_8ecec ra.                            (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - apply (regs_agree_strengthen sd_clob sd_clobx regs).
      + (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end). ra_solve.
      + intros i Hi Hni. cbn [sd_clobx In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma D2chain : forall (n : nat) r0 (cur : Z),
    (Z.to_nat cur < n)%nat -> (0 <= cur <= NIDS)%Z ->
    getr r0 11 = Z_to_bv 64 cur -> getr r0 19 = HSH -> getr r0 24 = MAP1 -> getr r0 22 = Z_to_bv 64 65535 ->
    regs_agree CLX regs r0 ->
    (exists r id, msteps segs (mkst r0 (at_ base 320) SM rom) (mkst r (at_ base 580) SM rom)
        /\ getr r 10 = Z_to_bv 64 id /\ (1 <= id <= NIDS)%Z /\ hashf id = HSH
        /\ (forall x : reg, In x [2; 8; 9; 18; 19; 20; 21; 23; 24; 25] -> getr r x = getr r0 x) /\ regs_agree CLX regs r)
    \/ (exists r, msteps segs (mkst r0 (at_ base 320) SM rom) (mkst r (at_ base 408) SM rom)
        /\ getr r 11 = Z_to_bv 64 0
        /\ (forall x : reg, In x [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25] -> getr r x = getr r0 x) /\ regs_agree CLX regs r).
  Proof using HC HD HD32 Hblk Hnids Hsp Hsz Htag Htr Rmap Rnode.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range D) as HDr.
    induction n as [|n IH]; intros r0 cur Hn Hcur R11 R19 R24 R22 AG0; [lia|].
    destruct (Z.eq_dec cur 0) as [-> | NZ].
    { right. wd_eexists. split.
      - ab_tk Xf24b8 D_8ebb8 ltac:(condz).              (* [comment removed for export] *)
        wd_refl.
      - post.
        all: first [ exact AG0 | (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
                   | intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx ]. }
    destruct (id16 cur Hcur) as (I1 & I2 & I3).
    destruct (Rmap (cur / 2 ^ 16) ltac:(lia)) as (Rblk & BNZ & BRNG). pose proof (Hblk (cur / 2 ^ 16) ltac:(lia)) as BPL.
    destruct (Rnode cur ltac:(lia)) as (Rh & Rl & Hl).
    set (blk := blkf (cur / 2 ^ 16)) in *. pose proof (u64_range blk) as Hblkr.
    assert (Rblk' : rdn segs SM (Z_to_bv 64 (U D + 4194320 + 8 * (cur / 2 ^ 16))) 8 = Some (LE8 blk)).
    { apply rd_o2; [wd_ulia_c | wd_ulia_c | exact Rblk]. }
    assert (Rh' : rdn segs SM (nd cur) 8 = Some (LE8 (hashf cur))).
    { apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rh]. }
    assert (Rl' : rdn segs SM (at_ (nd cur) 8) 4 = Some (LE4 (linkf cur))).
    { apply rd_o2; [(lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rl]. }
    (* [comment removed for export] *)
    assert (W : exists r1, msteps segs (mkst r0 (at_ base 320) SM rom) (mkst r1 (at_ base 376) SM rom)
                 /\ getr r1 10 = Z_to_bv 64 cur /\ getr r1 12 = hashf cur /\ getr r1 11 = Z_to_bv 64 (linkf cur)
                 /\ getr r1 19 = HSH /\ getr r1 24 = MAP1 /\ getr r1 22 = Z_to_bv 64 65535
                 /\ (forall x : reg, In x [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25] -> getr r1 x = getr r0 x) /\ regs_agree CLX regs r1).
    { wd_eexists. split.
      { ab_ft Xf24b8 D_8ebb8 ltac:(condz).              (* [comment removed for export] *)
        an Xf24bc D_8ebbc.                               (* [comment removed for export] *)
        an Xf24c0 D_8ebc0. rewrite v_srliw_bw by lia.     (* [comment removed for export] *)
        av Xf24c4 D_8ebc4 (Z_to_bv 64 (8 * (cur / 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
        av Xf24c8 D_8ebc8 (Z_to_bv 64 (U D + 4194320 + 8 * (cur / 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        cld2 Xf24cc D_8ebcc blk ltac:(exact Rblk').        (* [comment removed for export] *)
        ab_ft Xf24d0 D_8ebd0 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); fold blk; exact BNZ || (unorm; exact BNZ)).   (* [comment removed for export] *)
        av Xf24d4 D_8ebd4 (Z_to_bv 64 (cur * 2 ^ 32)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
        av Xf24d8 D_8ebd8 (Z_to_bv 64 cur) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite Z.div_mul by lia; reflexivity).  (* [comment removed for export] *)
        an Xf24dc D_8ebdc. rewrite (v_and_bw16 cur (Z_to_bv 64 cur)) by (lia || (unorm; reflexivity)).   (* [comment removed for export] *)
        av Xf24e0 D_8ebe0 (Z_to_bv 64 (16 * (cur mod 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
        av Xf24e4 D_8ebe4 (nd cur) ltac:((lazymatch goal with |- ?G => let G' := eval unfold nd in G in change_no_check G' end); fold blk; apply v_add_at; lia).   (* [comment removed for export] *)
        cld2 Xf24e8 D_8ebe8 (hashf cur) ltac:(exact Rh').   (* [comment removed for export] *)
        clw2 Xf24ec D_8ebec (linkf cur) ltac:(exact Rl').  (* [comment removed for export] *)
        wd_refl. }
      post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac
           end. }
    destruct W as (r1 & RUN1 & A10 & A12 & A11 & A19 & A24 & A22 & AK & AG1).
    destruct (decide (hashf cur = HSH)) as [EQ | NE].
    - (* [comment removed for export] *)
      left. exists r1, cur. 
      assert (W2 : msteps segs (mkst r1 (at_ base 376) SM rom) (mkst r1 (at_ base 580) SM rom)).
      { ab_ft Xf24f0 D_8ebf0 ltac:(rwH; rewrite EQ; (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
        an Xf24f4 D_8ebf4.                               (* [comment removed for export] *)
        wd_refl. }
      all: try (split; [eapply msteps_trans; [exact RUN1 | exact W2] |]; split; [exact A10|]; split; [lia|]; split; [exact EQ|]; split; [| exact AG1];
                intros x Hx; apply AK; cbn [In] in Hx |- *; clear - Hx; tauto).
    - (* [comment removed for export] *)
      assert (W2 : msteps segs (mkst r1 (at_ base 376) SM rom) (mkst r1 (at_ base 320) SM rom)).
      { ab_tk Xf24f0 D_8ebf0 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; intros E; apply NE; apply bv_eq; lia).   (* [comment removed for export] *)
        wd_refl. }
      destruct (IH r1 (linkf cur) ltac:(lia) ltac:(lia) A11 A19 A24 A22 AG1) as [(r & id & RUN & P10 & Pid & PH & PK & PAG) | (r & RUN & P11 & PK & PAG)].
      + left. exists r, id. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact W2 | exact RUN] |].
        split; [exact P10|]. split; [exact Pid|]. split; [exact PH|]. split; [| exact PAG].
        intros x Hx. rewrite (PK x Hx). apply AK. cbn [In] in Hx |- *; clear - Hx; tauto.
      + right. exists r. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact W2 | exact RUN] |].
        split; [exact P11|]. split; [| exact PAG].
        intros x Hx. rewrite (PK x Hx). apply AK. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Theorem sd_probe :
    (exists r id,
        msteps segs (mkst regs base mem rom) (mkst r ra SM rom)
        /\ getr r 10 = Z_to_bv 64 id /\ (1 <= id <= NIDS)%Z /\ hashf id = HSH
        /\ regs_agree CL regs r)
    \/ (exists r,
        msteps segs (mkst regs base mem rom) (mkst r (at_ base 408) SM rom)
        /\ getr r 2 = at_ sp (-112) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = D /\ getr r 11 = Z_to_bv 64 0
        /\ getr r 18 = Z_to_bv 64 (U D + 4 * BIX) /\ getr r 19 = HSH /\ getr r 20 = Z_to_bv 64 (U D + 4194312)
        /\ getr r 22 = Z_to_bv 64 65535 /\ getr r 23 = Z_to_bv 64 2147483647 /\ getr r 24 = MAP1 /\ getr r 25 = Z_to_bv 64 (tabf BIX)
        /\ regs_agree CLX regs r).
  Proof using A4 G128 G132 G148 H1 H10 H11 H2 HC HD HD32 Hblk Hcells Hnids Hret Hsp Hstk Hsz Htag Htr Rm Rm8 Rmap Rnode Rseed Rtab Rws.
    pose proof (bix_range HSH) as Hbix. destruct (Rtab BIX Hbix) as [_ Hbw].
    destruct D1 as (r1 & M1 & A2 & A9 & A11 & A12 & A13 & A15 & A16 & A10 & A8 & AG1).
    destruct (D2 r1 A9 A11 A12 A13 A15 A16 A10 AG1) as (r2 & M2 & B11 & B19 & B24 & B22 & B18 & B25 & B23 & B20 & B8 & BK & AG2).
    destruct (D2chain (S (Z.to_nat (tabf BIX))) r2 (tabf BIX) ltac:(lia) ltac:(lia) B11 B19 B24 B22 AG2)
      as [(r3 & id & M3 & C10 & Cid & CH & CK & AG3) | (r3 & M3 & C11 & CK & AG3)].
    - left.
      destruct (D3 r3 ltac:(rewrite (CK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite (BK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A2) AG3) as (r4 & M4 & E10 & AG4).
      exists r4, id. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4] |].
      split; [rewrite E10; exact C10|]. split; [exact Cid|]. split; [exact CH | exact AG4].
    - right. exists r3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact M3] |].

      split; [rewrite (CK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite (BK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A2|].
      split; [rewrite (CK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite B8; exact A8|].
      split; [rewrite (CK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); rewrite (BK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A9|].
      split; [exact C11|].
      split; [rewrite (CK 18) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B18|]. split; [rewrite (CK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B19|]. split; [rewrite (CK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B20|]. split; [rewrite (CK 22) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B22|].
      split; [rewrite (CK 23) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B23|]. split; [rewrite (CK 24) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B24|]. split; [rewrite (CK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact B25|]. exact AG3.
  Qed.
  End WithRegs.
End DEPOT.
End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
#[local] Unset Lia Cache.
Section FPGen2.
Context {fx : FPState}.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition asan_sd_tab : sd_tab := SDT (Z_to_bv 64 0x8ea80) (Z_to_bv 64 0x1e9458) 0x10350 0x10450 0x10310.

Lemma asan_sd_tab_ok : sd_tab_ok ASEGS asan_sd_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [st_base st_depot st_g_m8 st_g_seed st_g_m asan_sd_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold sdput_words in G in change_no_check G' end). code_ato_vm.
  - gaddr2_tac F_8ea7c D_8ea7c F_8ea80 D_8ea80.
  - gauipc_ld_tac F_8eaf8 D_8eaf8 F_8eb14 D_8eb14.
  - gauipc_ld_tac F_8eafc D_8eafc F_8eb04 D_8eb04.
  - gauipc_ld_tac F_8eb0c D_8eb0c F_8eb10 D_8eb10.
  - vm_compute. exact eq_refl.
Qed.

End FPGen2.
