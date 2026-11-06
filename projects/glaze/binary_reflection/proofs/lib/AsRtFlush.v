(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation W8 w := (word_to_le_bytes 8 w).

(* [comment removed for export] *)
Definition up4k (x : Z) : Z := ((x + 4095) / 4096 * 4096)%Z.
Definition down4k (x : Z) : Z := (x / 4096 * 4096)%Z.

Lemma land_m4k : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 12) = (a - a mod 4096)%Z.
Proof using.
  intros a Ha.
  replace (2 ^ 64 - 2 ^ 12)%Z with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2 ^ 12) ltac:(lia)). change (2 ^ 12)%Z with 4096%Z in *. lia.
Qed.
Lemma step_and_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_and (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof using.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Lemma v_and_m4k : forall x : word,
  v_and x (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) = Z_to_bv 64 (bv_unsigned x - bv_unsigned x mod 4096).
Proof using.
  intros x. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite (u_Z2bv (2 ^ 64 - 2 ^ 12)) by lia.
  rewrite land_m4k by lia. reflexivity.
Qed.
Ltac av_and F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

(* [comment removed for export] *)
Definition fl_sb (p : word) : Z := (bv_unsigned p / 8 + 0x7fff8000)%Z.
Definition fl_se (p size : word) : Z := ((bv_unsigned p + bv_unsigned size) / 8 + 0x7fff8000)%Z.

(* [comment removed for export] *)
Definition fl_frame (mem : word -> option byte) (S ra s0 s1 s2 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-8)) (W8 ra)) (at_ S (-16)) (W8 s0)) (at_ S (-24)) (W8 s1)) (at_ S (-32)) (W8 s2).

Ltac wb_side := wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia.

Lemma fl_frame_out : forall mem (S ra s0 s1 s2 a : word),
  (32 <= U S)%Z -> (U a < U S - 32 \/ U S <= U a)%Z -> fl_frame mem S ra s0 s1 s2 a = mem a.
Proof using.
  intros mem S ra s0 s1 s2 a Hsp Ha. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end).
  rewrite !MemsetLibF.MemSplit.wbytes_outside; [reflexivity | wb_side ..].
Qed.
Lemma fl_frame_grows : forall mem S ra s0 s1 s2, mem_grows mem (fl_frame mem S ra s0 s1 s2).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Lemma fl_frame_ok : forall segs mem S ra s0 s1 s2 (a : word) n,
  store_ok segs mem a n = true -> store_ok segs (fl_frame mem S ra s0 s1 s2) a n = true.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). repeat (eapply store_ok_mono; [apply wbytes_grows|]). assumption. Qed.
(* [comment removed for export] *)
Lemma fl_frame_in : forall mem mem' (S ra s0 s1 s2 a : word),
  (32 <= U S)%Z -> (U S - 32 <= U a < U S)%Z ->
  fl_frame mem S ra s0 s1 s2 a = fl_frame mem' S ra s0 s1 s2 a /\ fl_frame mem S ra s0 s1 s2 a <> None.
Proof using.
  intros mem mem' S ra s0 s1 s2 a Hsp Ha. pose proof (u64_range S). pose proof (u64_range a). (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end).
  destruct (Z_lt_le_dec (U a) (U S - 24)) as [C3|C3].
  { rewrite !MemsetLibF.MemSplit.wbytes_inside; [split; [reflexivity | discriminate] | wb_side ..]. }
  rewrite (MemsetLibF.MemSplit.wbytes_outside _ _ (at_ S (-32))); [| wb_side | wb_side].
  rewrite (MemsetLibF.MemSplit.wbytes_outside _ _ (at_ S (-32))); [| wb_side | wb_side].
  destruct (Z_lt_le_dec (U a) (U S - 16)) as [C4|C4].
  { rewrite !MemsetLibF.MemSplit.wbytes_inside; [split; [reflexivity | discriminate] | wb_side ..]. }
  rewrite (MemsetLibF.MemSplit.wbytes_outside _ _ (at_ S (-24))); [| wb_side | wb_side].
  rewrite (MemsetLibF.MemSplit.wbytes_outside _ _ (at_ S (-24))); [| wb_side | wb_side].
  destruct (Z_lt_le_dec (U a) (U S - 8)) as [C5|C5].
  { rewrite !MemsetLibF.MemSplit.wbytes_inside; [split; [reflexivity | discriminate] | wb_side ..]. }
  rewrite (MemsetLibF.MemSplit.wbytes_outside _ _ (at_ S (-16))); [| wb_side | wb_side].
  rewrite (MemsetLibF.MemSplit.wbytes_outside _ _ (at_ S (-16))); [| wb_side | wb_side].
  rewrite !MemsetLibF.MemSplit.wbytes_inside; [split; [reflexivity | discriminate] | wb_side ..].
Qed.
(* [comment removed for export] *)
Lemma fl_frame_mod : forall mem (S ra s0 s1 s2 a : word),
  (32 <= U S)%Z -> fl_frame mem S ra s0 s1 s2 a <> mem a ->
  (U S - 32 <= U a < U S)%Z /\ fl_frame mem S ra s0 s1 s2 a <> None.
Proof using.
  intros mem S ra s0 s1 s2 a Hsp NE. pose proof (u64_range S). pose proof (u64_range a).
  destruct (Z_lt_le_dec (U a) (U S - 32)) as [C1|C1].
  { exfalso. apply NE. apply fl_frame_out; lia. }
  destruct (Z_lt_le_dec (U a) (U S)) as [C2|C2].
  2:{ exfalso. apply NE. apply fl_frame_out; lia. }
  split; [lia|]. exact (proj2 (fl_frame_in mem mem S ra s0 s1 s2 a Hsp ltac:(lia))).
Qed.
(* [comment removed for export] *)
Lemma fl_frame_idem : forall mem (S ra s0 s1 s2 : word), (32 <= U S)%Z ->
  fl_frame (fl_frame mem S ra s0 s1 s2) S ra s0 s1 s2 = fl_frame mem S ra s0 s1 s2.
Proof using.
  intros mem S ra s0 s1 s2 Hsp. apply functional_extensionality. intros a. pose proof (u64_range S). pose proof (u64_range a).
  destruct (Z_lt_le_dec (U a) (U S - 32)) as [C1|C1]; [rewrite fl_frame_out by lia; reflexivity|].
  destruct (Z_lt_le_dec (U a) (U S)) as [C2|C2]; [|rewrite fl_frame_out by lia; reflexivity].
  exact (proj1 (fl_frame_in (fl_frame mem S ra s0 s1 s2) mem S ra s0 s1 s2 a Hsp ltac:(lia))).
Qed.
Lemma rd_fl_frame : forall segs mem (S ra s0 s1 s2 : word) c n bs, (32 <= U S)%Z -> (0 <= c)%Z -> (c + Z.of_nat n <= U S - 32)%Z ->
  rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs (fl_frame mem S ra s0 s1 s2) (Z_to_bv 64 c) n = Some bs.
Proof using.
  intros segs mem S ra s0 s1 s2 c n bs Hsp Hc0 Hc Hr. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end).
  rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try lia.
  exact Hr.
Qed.
Lemma fl_frame_mrestrict : forall (Hd : word -> bool) mem (S ra s0 s1 s2 : word),
  (32 <= U S)%Z -> hid_off Hd (U S - 32) 32 ->
  fl_frame (mrestrict Hd mem) S ra s0 s1 s2 = mrestrict Hd (fl_frame mem S ra s0 s1 s2).
Proof using.
  intros Hd mem S ra s0 s1 s2 Hsp HOFF. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end).
  rewrite !wbytes_mrestrict; [reflexivity | | | | | | | |];
    wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HOFF; lia].
Qed.

(* [comment removed for export] *)
Lemma fl_geom : forall (p size : word),
  ((0x10007fff8000 <= U p + U size \/ U p + U size <= 0x7fff7fff) /\ U p + U size <= 0x7fffffffffff)%Z ->
  (0x7fff8000 <= fl_sb p /\ fl_sb p <= fl_se p size /\ fl_se p size <= 0x10007fff8000 /\ fl_sb p <= up4k (fl_sb p) /\ up4k (fl_sb p) <= fl_sb p + 4095
   /\ fl_se p size - 4095 <= down4k (fl_se p size) /\ down4k (fl_se p size) <= fl_se p size
   /\ up4k (fl_sb p) mod 4096 = 0 /\ down4k (fl_se p size) mod 4096 = 0 /\ 0 <= down4k (fl_se p size))%Z.
Proof using.
  intros p size Hend.
    (lazymatch goal with |- ?G => let G' := eval unfold fl_sb, fl_se, up4k, down4k in G in change_no_check G' end). pose proof (u64_range p) as Hp. pose proof (u64_range size) as Hs.
    destruct Hend as [_ He].
    pose proof (Z.div_pos (U p) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (U p) (U p + U size) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (U p + U size) 0x7fffffffffff 8 ltac:(lia) He) as D3. change (0x7fffffffffff / 8)%Z with 17592186044415%Z in D3.
    pose proof (Z.div_mod (U p / 8 + 2147450880 + 4095) 4096 ltac:(lia)).
    pose proof (Z.mod_pos_bound (U p / 8 + 2147450880 + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod ((U p + U size) / 8 + 2147450880) 4096 ltac:(lia)).
    pose proof (Z.mod_pos_bound ((U p + U size) / 8 + 2147450880) 4096 ltac:(lia)).
    pose proof (Z.div_pos ((U p + U size) / 8 + 2147450880) 4096 ltac:(lia) ltac:(lia)).
    repeat split; try lia; apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Definition flush_words : list (option (bv 32)) :=
  [
   Some W_6dff0; Some W_6dff4; Some W_6dff8; Some W_6dffc; Some W_6e000; Some W_6e004; Some W_6e008; Some W_6e00c;
   Some W_6e010; Some W_6e014; Some W_6e018; Some W_6e01c; Some W_6e020; Some W_6e024; Some W_6e028; Some W_6e02c;
   Some W_6e030; Some W_6e034; Some W_6e038
  ]%list.

(* [comment removed for export] *)
Definition rel_words : list (option (bv 32)) :=
  [
   Some W_89b30; Some W_89b34; Some W_89b38; Some W_89b3c; Some W_89b40; Some W_89b44; None; None; Some W_89b50;
   Some W_89b54; Some W_89b58; Some W_89b5c; Some W_89b60; Some W_89b64; Some W_89b68; Some W_89b6c; Some W_89b70;
   Some W_89b74; Some W_89b78; Some W_89b7c; Some W_89b80; Some W_89b84; Some W_89b88; Some W_89b8c; Some W_89b90;
   Some W_89b94; Some W_89b98; Some W_89b9c; Some W_89ba0; Some W_89ba4; Some W_89ba8; Some W_89bac; Some W_89bb0;
   Some W_89bb4; Some W_89bb8; Some W_89bbc; Some W_89bc0
  ]%list.

(* [comment removed for export] *)
Definition imadv_words : list (option (bv 32)) :=
  [
   None; None; Some W_80760; Some W_80764; Some W_80768; Some W_8076c; Some W_80770; Some W_80774; Some W_80778;
   Some W_8077c; Some W_80780
  ]%list.

Section FLUSH.
  Variables (segs : list Segment) (base : word).
  Variable mt : m2s_tab.
  Variables (g_pgsz p_pgsz g_seal sv : Z).
  Hypothesis HCF : code_ato segs base 0 flush_words.
  Hypothesis HCR : code_ato segs base 113472 rel_words.
  Hypothesis HCI : code_ato segs base 75624 imadv_words.
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ base 76.
  Hypothesis G113456 : gload2 segs base 113496 11 18 g_pgsz.    (* [comment removed for export] *)
  Hypothesis G756ac : gload segs base 75624 13 g_seal.          (* [comment removed for export] *)
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (U base + 120000 < 2 ^ 64)%Z.


  Lemma F_6dff0 : fetch_word segs (at_ base 0) = Some W_6dff0.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 0 _ HCF eq_refl). Qed.
  Lemma F_6dff4 : fetch_word segs (at_ base 4) = Some W_6dff4.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 1 _ HCF eq_refl). Qed.
  Lemma F_6dff8 : fetch_word segs (at_ base 8) = Some W_6dff8.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 2 _ HCF eq_refl). Qed.
  Lemma F_6dffc : fetch_word segs (at_ base 12) = Some W_6dffc.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 3 _ HCF eq_refl). Qed.
  Lemma F_6e000 : fetch_word segs (at_ base 16) = Some W_6e000.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 4 _ HCF eq_refl). Qed.
  Lemma F_6e004 : fetch_word segs (at_ base 20) = Some W_6e004.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 5 _ HCF eq_refl). Qed.
  Lemma F_6e008 : fetch_word segs (at_ base 24) = Some W_6e008.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 6 _ HCF eq_refl). Qed.
  Lemma F_6e00c : fetch_word segs (at_ base 28) = Some W_6e00c.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 7 _ HCF eq_refl). Qed.
  Lemma F_6e010 : fetch_word segs (at_ base 32) = Some W_6e010.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 8 _ HCF eq_refl). Qed.
  Lemma F_6e014 : fetch_word segs (at_ base 36) = Some W_6e014.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 9 _ HCF eq_refl). Qed.
  Lemma F_6e018 : fetch_word segs (at_ base 40) = Some W_6e018.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 10 _ HCF eq_refl). Qed.
  Lemma F_6e01c : fetch_word segs (at_ base 44) = Some W_6e01c.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 11 _ HCF eq_refl). Qed.
  Lemma F_6e020 : fetch_word segs (at_ base 48) = Some W_6e020.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 12 _ HCF eq_refl). Qed.
  Lemma F_6e024 : fetch_word segs (at_ base 52) = Some W_6e024.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 13 _ HCF eq_refl). Qed.
  Lemma F_6e028 : fetch_word segs (at_ base 56) = Some W_6e028.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 14 _ HCF eq_refl). Qed.
  Lemma F_6e02c : fetch_word segs (at_ base 60) = Some W_6e02c.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 15 _ HCF eq_refl). Qed.
  Lemma F_6e030 : fetch_word segs (at_ base 64) = Some W_6e030.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 16 _ HCF eq_refl). Qed.
  Lemma F_6e034 : fetch_word segs (at_ base 68) = Some W_6e034.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 17 _ HCF eq_refl). Qed.
  Lemma F_6e038 : fetch_word segs (at_ base 72) = Some W_6e038.   (* [comment removed for export] *)
  Proof using HCF. exact (code_ato_get segs base 0 flush_words 18 _ HCF eq_refl). Qed.


  Lemma F_89b30 : fetch_word segs (at_ base 113472) = Some W_89b30.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 0 _ HCR eq_refl). Qed.
  Lemma F_89b34 : fetch_word segs (at_ base 113476) = Some W_89b34.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 1 _ HCR eq_refl). Qed.
  Lemma F_89b38 : fetch_word segs (at_ base 113480) = Some W_89b38.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 2 _ HCR eq_refl). Qed.
  Lemma F_89b3c : fetch_word segs (at_ base 113484) = Some W_89b3c.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 3 _ HCR eq_refl). Qed.
  Lemma F_89b40 : fetch_word segs (at_ base 113488) = Some W_89b40.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 4 _ HCR eq_refl). Qed.
  Lemma F_89b44 : fetch_word segs (at_ base 113492) = Some W_89b44.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 5 _ HCR eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_89b50 : fetch_word segs (at_ base 113504) = Some W_89b50.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 8 _ HCR eq_refl). Qed.
  Lemma F_89b54 : fetch_word segs (at_ base 113508) = Some W_89b54.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 9 _ HCR eq_refl). Qed.
  Lemma F_89b58 : fetch_word segs (at_ base 113512) = Some W_89b58.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 10 _ HCR eq_refl). Qed.



  Lemma F_89b68 : fetch_word segs (at_ base 113528) = Some W_89b68.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 14 _ HCR eq_refl). Qed.
  Lemma F_89b6c : fetch_word segs (at_ base 113532) = Some W_89b6c.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 15 _ HCR eq_refl). Qed.
  Lemma F_89b70 : fetch_word segs (at_ base 113536) = Some W_89b70.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 16 _ HCR eq_refl). Qed.
  Lemma F_89b74 : fetch_word segs (at_ base 113540) = Some W_89b74.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 17 _ HCR eq_refl). Qed.
  Lemma F_89b78 : fetch_word segs (at_ base 113544) = Some W_89b78.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 18 _ HCR eq_refl). Qed.
  Lemma F_89b7c : fetch_word segs (at_ base 113548) = Some W_89b7c.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 19 _ HCR eq_refl). Qed.
  Lemma F_89b80 : fetch_word segs (at_ base 113552) = Some W_89b80.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 20 _ HCR eq_refl). Qed.
  Lemma F_89b84 : fetch_word segs (at_ base 113556) = Some W_89b84.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 21 _ HCR eq_refl). Qed.
  Lemma F_89b88 : fetch_word segs (at_ base 113560) = Some W_89b88.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 22 _ HCR eq_refl). Qed.
  Lemma F_89b8c : fetch_word segs (at_ base 113564) = Some W_89b8c.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 23 _ HCR eq_refl). Qed.
  Lemma F_89b90 : fetch_word segs (at_ base 113568) = Some W_89b90.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 24 _ HCR eq_refl). Qed.
  Lemma F_89b94 : fetch_word segs (at_ base 113572) = Some W_89b94.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 25 _ HCR eq_refl). Qed.
  Lemma F_89b98 : fetch_word segs (at_ base 113576) = Some W_89b98.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 26 _ HCR eq_refl). Qed.
  Lemma F_89b9c : fetch_word segs (at_ base 113580) = Some W_89b9c.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 27 _ HCR eq_refl). Qed.
  Lemma F_89ba0 : fetch_word segs (at_ base 113584) = Some W_89ba0.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 28 _ HCR eq_refl). Qed.
  Lemma F_89ba4 : fetch_word segs (at_ base 113588) = Some W_89ba4.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 29 _ HCR eq_refl). Qed.
  Lemma F_89ba8 : fetch_word segs (at_ base 113592) = Some W_89ba8.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 30 _ HCR eq_refl). Qed.
  Lemma F_89bac : fetch_word segs (at_ base 113596) = Some W_89bac.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 31 _ HCR eq_refl). Qed.
  Lemma F_89bb0 : fetch_word segs (at_ base 113600) = Some W_89bb0.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 32 _ HCR eq_refl). Qed.
  Lemma F_89bb4 : fetch_word segs (at_ base 113604) = Some W_89bb4.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 33 _ HCR eq_refl). Qed.
  Lemma F_89bb8 : fetch_word segs (at_ base 113608) = Some W_89bb8.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 34 _ HCR eq_refl). Qed.
  Lemma F_89bbc : fetch_word segs (at_ base 113612) = Some W_89bbc.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 35 _ HCR eq_refl). Qed.
  Lemma F_89bc0 : fetch_word segs (at_ base 113616) = Some W_89bc0.   (* [comment removed for export] *)
  Proof using HCR. exact (code_ato_get segs base 113472 rel_words 36 _ HCR eq_refl). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_80760 : fetch_word segs (at_ base 75632) = Some W_80760.   (* [comment removed for export] *)
  Proof using HCI. exact (code_ato_get segs base 75624 imadv_words 2 _ HCI eq_refl). Qed.
  Lemma F_80764 : fetch_word segs (at_ base 75636) = Some W_80764.   (* [comment removed for export] *)
  Proof using HCI. exact (code_ato_get segs base 75624 imadv_words 3 _ HCI eq_refl). Qed.
  Lemma F_80768 : fetch_word segs (at_ base 75640) = Some W_80768.   (* [comment removed for export] *)
  Proof using HCI. exact (code_ato_get segs base 75624 imadv_words 4 _ HCI eq_refl). Qed.


  Lemma F_80774 : fetch_word segs (at_ base 75652) = Some W_80774.   (* [comment removed for export] *)
  Proof using HCI. exact (code_ato_get segs base 75624 imadv_words 7 _ HCI eq_refl). Qed.




  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables (ra S p size midend : word).
  #[local] Abbreviation LE8' z := (word_to_le_bytes 8 (Z_to_bv 64 z)).
  (* [comment removed for export] *)
  Hypothesis PH : m2sH segs mt mem p midend.
  Hypothesis Hend : ((0x10007fff8000 <= U p + U size \/ U p + U size <= 0x7fff7fff) /\ U p + U size <= 0x7fffffffffff)%Z.
  Hypothesis Rg_pgsz : rdn segs mem (Z_to_bv 64 g_pgsz) 8 = Some (LE8' p_pgsz).
  Hypothesis Rpgsz : rdn segs mem (Z_to_bv 64 p_pgsz) 8 = Some (LE8' 4096).
  Hypothesis Rg_seal : rdn segs mem (Z_to_bv 64 g_seal) 8 = Some (LE8' sv).
  Hypothesis Hsv : (0 < sv < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Definition fl_cells : list Z := ([g_pgsz; p_pgsz; g_seal] ++ m2s_cells mt)%Z.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U S - 32)%Z fl_cells.
  Hypothesis HS : (32 <= U S)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ S (-32)) 32 = true.
  Hypothesis Hret : ret_ok ra.

  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = S.
  Hypothesis H10 : getr regs 10 = p.
  Hypothesis H11 : getr regs 11 = size.

  (* [comment removed for export] *)
  #[local] Abbreviation SBz := (fl_sb p).
  #[local] Abbreviation SEz := (fl_se p size).
  #[local] Abbreviation PBz := (up4k (fl_sb p)).
  #[local] Abbreviation PEz := (down4k (fl_se p size)).
  (* [comment removed for export] *)
  Definition MFL : word -> option byte := fl_frame mem S ra (getr regs 8) (getr regs 9) (getr regs 18).


  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold fl_cells, m2s_cells in HC; cbn [app] in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.

  (* [comment removed for export] *)
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | (lazymatch goal with |- ?G => let G' := eval unfold MFL in G in change_no_check G' end); repeat (eapply store_ok_mono; [first [apply wbytes_grows | apply fl_frame_grows]|]);
          eapply (store_ok_sub segs mem (at_ S (-32)) _ 32);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac rd_thru Hr :=
    lazymatch goal with
    | |- rdn _ ?m _ _ = _ =>
        lazymatch m with
        | mem => exact Hr
        | MFL => (lazymatch goal with |- ?G => let G' := eval unfold MFL in G in change_no_check G' end); apply rd_fl_frame; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia | exact Hr]
        | fl_frame _ _ _ _ _ _ => apply rd_fl_frame; [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia | exact Hr]
        end
    end.
  Ltac cld F D cc vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            replace a with (Z_to_bv 64 cc : word) by (rewrite ?v_addi_0; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); unorm; f_equal; lia) end;
          rd_thru Hr
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac fld F D vv :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold MFL, fl_frame in G in change_no_check G' end); rd8_chain
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma PH_MFL : m2sH segs mt MFL p midend.
  Proof using HS Hcells PH g_seal p_pgsz g_pgsz base.
    pose proof (u64_range S) as HSr. cells_split.
    destruct PH as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
    constructor; try assumption; (lazymatch goal with |- ?G => let G' := eval unfold MFL in G in change_no_check G' end); apply rd_fl_frame; try assumption; try lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia.
  Qed.
  Lemma PH_MFL_end : m2sH segs mt MFL (Z_to_bv 64 (U p + U size)) midend.
  Proof using HS Hcells Hend PH g_seal p_pgsz g_pgsz base.
    pose proof PH_MFL as [R1 R2 R3 R4 R5 R6 R7 R8 HC Hlo Hhi]. destruct Hend as [E1 E2].
    assert (UE : U (Z_to_bv 64 (U p + U size)) = (U p + U size)%Z) by (pose proof (u64_range p); pose proof (u64_range size); rewrite u_Z2bv; lia).
    constructor; try assumption; rewrite UE; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkF1 :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 76) MFL rom)
      /\ getr r 10 = p /\ getr r 1 = at_ base 32 /\ getr r 2 = at_ S (-32)
      /\ getr r 8 = size /\ getr r 9 = p /\ getr r 18 = getr regs 18
      /\ regs_agree (fun x => In x [1; 2; 8; 9]%list) regs r.
  Proof using H11 H10 H2 H1 Hstk HS Hbase HCF.
    pose proof (u64_range S) as HSr. destruct Hbase as [Hb2 Hb64].
    wd_eexists. split.
    - an F_6dff0 D_6dff0.                                      (* [comment removed for export] *)
      fsd F_6dff4 D_6dff4 (at_ S (-8)).                       (* [comment removed for export] *)
      fsd F_6dff8 D_6dff8 (at_ S (-16)).                      (* [comment removed for export] *)
      fsd F_6dffc D_6dffc (at_ S (-24)).                      (* [comment removed for export] *)
      fsd F_6e000 D_6e000 (at_ S (-32)).                      (* [comment removed for export] *)
      change (wbytes _ _ _) with MFL.
      an F_6e004 D_6e004.                                      (* [comment removed for export] *)
      an F_6e008 D_6e008.                                      (* [comment removed for export] *)
      an F_6e00c D_6e00c.                                      (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma blkF2 : forall r1,
    getr r1 10 = Z_to_bv 64 SBz -> getr r1 2 = at_ S (-32) -> getr r1 8 = size -> getr r1 9 = p ->
    exists r,
      msteps segs (mkst r1 (at_ base 32) MFL rom) (mkst r (at_ base 76) MFL rom)
      /\ getr r 10 = Z_to_bv 64 (U p + U size) /\ getr r 1 = at_ base 44 /\ getr r 2 = at_ S (-32)
      /\ getr r 18 = Z_to_bv 64 SBz
      /\ regs_agree (fun x => In x [1; 10; 18]%list) r1 r.
  Proof using Hend HCF.
    intros r1 Q10 Q2 Q8 Q9. pose proof (u64_range p) as Hpr. pose proof (u64_range size) as Hsr. destruct Hend as [_ He].
    wd_eexists. split.
    - an F_6e010 D_6e010.                                      (* [comment removed for export] *)
      av F_6e014 D_6e014 (Z_to_bv 64 (U p + U size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); f_equal; lia).   (* [comment removed for export] *)
      an F_6e018 D_6e018.                                      (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  Definition FLCLOB : list reg := [1; 2; 8; 9; 18; 10; 11; 12; 13; 17]%list.

  (* [comment removed for export] *)
  Lemma blkF3 : forall r3,
    getr r3 10 = Z_to_bv 64 SEz -> getr r3 2 = at_ S (-32) -> getr r3 18 = Z_to_bv 64 SBz ->
    (PBz < PEz)%Z ->
    exists r,
      msteps segs (mkst r3 (at_ base 44) MFL rom) (mkst r (at_ base 75656) MFL rom)
      /\ getr r 17 = Z_to_bv 64 233 /\ getr r 10 = Z_to_bv 64 PBz /\ getr r 11 = Z_to_bv 64 (PEz - PBz) /\ getr r 12 = Z_to_bv 64 4
      /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18
      /\ regs_agree (fun x => In x FLCLOB) r3 r.
  Proof using Hstk HS Hcells Hsv Rg_seal Rpgsz Rg_pgsz Hend Hbase G756ac G113456 HCI HCR HCF sv g_seal p_pgsz g_pgsz mt.
    intros r3 Q10 Q2 Q18 HLT. pose proof (u64_range S) as HSr. destruct Hbase as [Hb2 Hb64]. cells_split.
    pose proof (fl_geom p size Hend) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    destruct G113456 as [x113496 GX].
    wd_eexists. split.
    - an F_6e01c D_6e01c.                                      (* [comment removed for export] *)
      an F_6e020 D_6e020.                                      (* [comment removed for export] *)
      fld F_6e024 D_6e024 ra.                                  (* [comment removed for export] *)
      fld F_6e028 D_6e028 (getr regs 8).                       (* [comment removed for export] *)
      fld F_6e02c D_6e02c (getr regs 9).                       (* [comment removed for export] *)
      fld F_6e030 D_6e030 (getr regs 18).                      (* [comment removed for export] *)
      an F_6e034 D_6e034.                                      (* [comment removed for export] *)
      an F_6e038 D_6e038.                                      (* [comment removed for export] *)
      an F_89b30 D_89b30.                                      (* [comment removed for export] *)
      fsd F_89b34 D_89b34 (at_ S (-8)).                       (* [comment removed for export] *)
      fsd F_89b38 D_89b38 (at_ S (-16)).                      (* [comment removed for export] *)
      fsd F_89b3c D_89b3c (at_ S (-24)).                      (* [comment removed for export] *)
      fsd F_89b40 D_89b40 (at_ S (-32)).                      (* [comment removed for export] *)
      change (wbytes _ _ _) with (fl_frame MFL S ra (getr regs 8) (getr regs 9) (getr regs 18)).
      unfold MFL at 1. rewrite (fl_frame_idem mem S ra (getr regs 8) (getr regs 9) (getr regs 18) HS). fold MFL.
      an F_89b44 D_89b44.                                      (* [comment removed for export] *)
      eapply msteps_trans; [eapply GX; rd_thru Rg_pgsz|]; zlit_at.          (* [comment removed for export] *)
      cld F_89b50 D_89b50 p_pgsz (Z_to_bv 64 4096) Rpgsz.      (* [comment removed for export] *)
      an F_89b54 D_89b54.                                      (* [comment removed for export] *)
      ab_tk F_89b58 D_89b58 ltac:(condz).                      (* [comment removed for export] *)
      an F_89b68 D_89b68.                                      (* [comment removed for export] *)
      an F_89b6c D_89b6c.                                      (* [comment removed for export] *)
      ab_ft F_89b70 D_89b70 ltac:(condz).                      (* [comment removed for export] *)
      av F_89b74 D_89b74 (Z_to_bv 64 (SBz + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).     (* [comment removed for export] *)
      av F_89b78 D_89b78 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_89b7c D_89b7c (Z_to_bv 64 (SBz + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).    (* [comment removed for export] *)
      av_and F_89b80 D_89b80 (Z_to_bv 64 PBz)
         ltac:(rewrite v_and_m4k; unorm; (lazymatch goal with |- ?G => let G' := eval unfold up4k in G in change_no_check G' end); f_equal; pose proof (Z.div_mod (SBz + 4095) 4096 ltac:(lia)); lia).   (* [comment removed for export] *)
      av_and F_89b84 D_89b84 (Z_to_bv 64 PEz)
         ltac:(rewrite v_and_m4k; unorm; (lazymatch goal with |- ?G => let G' := eval unfold down4k in G in change_no_check G' end); f_equal; pose proof (Z.div_mod SEz 4096 ltac:(lia)); lia).          (* [comment removed for export] *)
      ab_ft F_89b88 D_89b88 ltac:(condz).                      (* [comment removed for export] *)
      av F_89b8c D_89b8c (Z_to_bv 64 (PEz - PBz)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; reflexivity).       (* [comment removed for export] *)
      an F_89b90 D_89b90.                                      (* [comment removed for export] *)
      fld F_89b94 D_89b94 ra.                                  (* [comment removed for export] *)
      fld F_89b98 D_89b98 (getr regs 8).                       (* [comment removed for export] *)
      fld F_89b9c D_89b9c (getr regs 9).                       (* [comment removed for export] *)
      fld F_89ba0 D_89ba0 (getr regs 18).                      (* [comment removed for export] *)
      an F_89ba4 D_89ba4.                                      (* [comment removed for export] *)
      an F_89ba8 D_89ba8.                                      (* [comment removed for export] *)
      eapply msteps_trans; [eapply G756ac; rd_thru Rg_seal|]; zlit_at.      (* [comment removed for export] *)
      ab_ft F_80760 D_80760 ltac:(condz).                      (* [comment removed for export] *)
      an F_80764 D_80764.                                      (* [comment removed for export] *)
      ab_tk F_80768 D_80768 ltac:(condz).                      (* [comment removed for export] *)
      an F_80774 D_80774.                                      (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold FLCLOB in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma blkF3n : forall r3,
    getr r3 10 = Z_to_bv 64 SEz -> getr r3 2 = at_ S (-32) -> getr r3 18 = Z_to_bv 64 SBz ->
    (PEz <= PBz)%Z ->
    exists r,
      msteps segs (mkst r3 (at_ base 44) MFL rom) (mkst r ra MFL rom)
      /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18
      /\ regs_agree (fun x => In x FLCLOB) r3 r.
  Proof using Hret Hstk HS Hcells Rpgsz Rg_pgsz Hend Hbase G113456 HCR HCF g_seal p_pgsz g_pgsz mt.
    intros r3 Q10 Q2 Q18 HGE. pose proof (u64_range S) as HSr. destruct Hbase as [Hb2 Hb64]. cells_split.
    pose proof (fl_geom p size Hend) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    destruct G113456 as [x113496 GX].
    wd_eexists. split.
    - an F_6e01c D_6e01c.                                      (* [comment removed for export] *)
      an F_6e020 D_6e020.                                      (* [comment removed for export] *)
      fld F_6e024 D_6e024 ra.                                  (* [comment removed for export] *)
      fld F_6e028 D_6e028 (getr regs 8).                       (* [comment removed for export] *)
      fld F_6e02c D_6e02c (getr regs 9).                       (* [comment removed for export] *)
      fld F_6e030 D_6e030 (getr regs 18).                      (* [comment removed for export] *)
      an F_6e034 D_6e034.                                      (* [comment removed for export] *)
      an F_6e038 D_6e038.                                      (* [comment removed for export] *)
      an F_89b30 D_89b30.                                      (* [comment removed for export] *)
      fsd F_89b34 D_89b34 (at_ S (-8)).                       (* [comment removed for export] *)
      fsd F_89b38 D_89b38 (at_ S (-16)).                      (* [comment removed for export] *)
      fsd F_89b3c D_89b3c (at_ S (-24)).                      (* [comment removed for export] *)
      fsd F_89b40 D_89b40 (at_ S (-32)).                      (* [comment removed for export] *)
      change (wbytes _ _ _) with (fl_frame MFL S ra (getr regs 8) (getr regs 9) (getr regs 18)).
      unfold MFL at 1. rewrite (fl_frame_idem mem S ra (getr regs 8) (getr regs 9) (getr regs 18) HS). fold MFL.
      an F_89b44 D_89b44.                                      (* [comment removed for export] *)
      eapply msteps_trans; [eapply GX; rd_thru Rg_pgsz|]; zlit_at.          (* [comment removed for export] *)
      cld F_89b50 D_89b50 p_pgsz (Z_to_bv 64 4096) Rpgsz.      (* [comment removed for export] *)
      an F_89b54 D_89b54.                                      (* [comment removed for export] *)
      ab_tk F_89b58 D_89b58 ltac:(condz).                      (* [comment removed for export] *)
      an F_89b68 D_89b68.                                      (* [comment removed for export] *)
      an F_89b6c D_89b6c.                                      (* [comment removed for export] *)
      ab_ft F_89b70 D_89b70 ltac:(condz).                      (* [comment removed for export] *)
      av F_89b74 D_89b74 (Z_to_bv 64 (SBz + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).     (* [comment removed for export] *)
      av F_89b78 D_89b78 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_89b7c D_89b7c (Z_to_bv 64 (SBz + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).    (* [comment removed for export] *)
      av_and F_89b80 D_89b80 (Z_to_bv 64 PBz)
         ltac:(rewrite v_and_m4k; unorm; (lazymatch goal with |- ?G => let G' := eval unfold up4k in G in change_no_check G' end); f_equal; pose proof (Z.div_mod (SBz + 4095) 4096 ltac:(lia)); lia).   (* [comment removed for export] *)
      av_and F_89b84 D_89b84 (Z_to_bv 64 PEz)
         ltac:(rewrite v_and_m4k; unorm; (lazymatch goal with |- ?G => let G' := eval unfold down4k in G in change_no_check G' end); f_equal; pose proof (Z.div_mod SEz 4096 ltac:(lia)); lia).          (* [comment removed for export] *)
      ab_tk F_89b88 D_89b88 ltac:(condz).                      (* [comment removed for export] *)
      fld F_89bac D_89bac ra.                                  (* [comment removed for export] *)
      fld F_89bb0 D_89bb0 (getr regs 8).                       (* [comment removed for export] *)
      fld F_89bb4 D_89bb4 (getr regs 9).                       (* [comment removed for export] *)
      fld F_89bb8 D_89bb8 (getr regs 18).                      (* [comment removed for export] *)
      an F_89bbc D_89bbc.                                      (* [comment removed for export] *)
      aret F_89bc0 D_89bc0 ra.                                 (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold FLCLOB in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FLBIG : list reg := (1 :: 2 :: 8 :: 9 :: 18 :: m2s_clob)%list.

  Lemma FLBIG_sub1 : forall x : reg, In x [1; 2; 8; 9]%list -> In x FLBIG.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold FLBIG, m2s_clob in G in change_no_check G' end). incl_lists. Qed.
  Lemma FLBIG_sub2 : forall x : reg, In x m2s_clob -> In x FLBIG.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold FLBIG, m2s_clob in G in change_no_check G' end). incl_lists. Qed.
  Lemma FLBIG_sub3 : forall x : reg, In x [1; 10; 18]%list -> In x FLBIG.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold FLBIG, m2s_clob in G in change_no_check G' end). incl_lists. Qed.
  Lemma FLBIG_sub4 : forall x : reg, In x FLCLOB -> In x FLBIG.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold FLBIG, FLCLOB, m2s_clob in G in change_no_check G' end). incl_lists. Qed.

  (* [comment removed for export] *)
  Lemma flush_head :
    exists r3,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r3 (at_ base 44) MFL rom)
      /\ getr r3 10 = Z_to_bv 64 SEz /\ getr r3 2 = at_ S (-32) /\ getr r3 18 = Z_to_bv 64 SBz
      /\ regs_agree (fun x => In x FLBIG) regs r3.
  Proof using H11 H10 H2 H1 Hstk HS Hcells Hend PH midend Hbase MTB MTOK HCF g_seal p_pgsz g_pgsz mt.
    destruct Hbase as [Hb2 Hb64].
    assert (RT32 : ret_ok (at_ base 32)) by (apply ret_ok_at; [exact Hb2 | reflexivity | pose proof (u64_range base); lia]).
    assert (RT44 : ret_ok (at_ base 44)) by (apply ret_ok_at; [exact Hb2 | reflexivity | pose proof (u64_range base); lia]).
    destruct blkF1 as (r0 & RUN0 & A10 & A1 & A2 & A8 & A9 & A18 & AG0).
    destruct (m2s_run segs mt MTOK MFL rom p midend (at_ base 32) r0 PH_MFL A10 A1 RT32) as (r1 & RUN1 & B10 & AG1).
    assert (B2 : getr r1 2 = at_ S (-32)) by (rewrite (AG1 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact A2).
    assert (B8 : getr r1 8 = size) by (rewrite (AG1 8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact A8).
    assert (B9 : getr r1 9 = p) by (rewrite (AG1 9 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact A9).
    destruct (blkF2 r1 B10 B2 B8 B9) as (r2 & RUN2 & C10 & C1 & C2 & C18 & AG2).
    destruct (m2s_run segs mt MTOK MFL rom (Z_to_bv 64 (U p + U size)) midend (at_ base 44) r2 PH_MFL_end C10 C1 RT44) as (r3 & RUN3 & D10 & AG3).
    assert (D2 : getr r3 2 = at_ S (-32)) by (rewrite (AG3 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C2).
    assert (D18 : getr r3 18 = Z_to_bv 64 SBz) by (rewrite (AG3 18 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C18).
    exists r3. split; [|split; [|split; [exact D2 | split; [exact D18|]]]].
    - rewrite MTB in RUN1, RUN3.
      eapply msteps_trans; [exact RUN0|]. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - rewrite D10. (lazymatch goal with |- ?G => let G' := eval unfold fl_se in G in change_no_check G' end). pose proof (u64_range p). pose proof (u64_range size). destruct Hend as [_ He]. rewrite u_Z2bv by lia. reflexivity.
    - eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans|]|].
      + exact (regs_agree_mono _ _ _ _ FLBIG_sub1 AG0).
      + exact (regs_agree_mono _ _ _ _ FLBIG_sub2 AG1).
      + exact (regs_agree_mono _ _ _ _ FLBIG_sub3 AG2).
      + exact (regs_agree_mono _ _ _ _ FLBIG_sub2 AG3).
  Qed.

  (* [comment removed for export] *)
  Lemma fl_clob_final : forall r,
    regs_agree (fun x => In x FLBIG) regs r ->
    getr r 1 = ra -> getr r 2 = S -> getr r 8 = getr regs 8 -> getr r 9 = getr regs 9 -> getr r 18 = getr regs 18 ->
    regs_agree (fun x => In x m2s_clob) regs r.
  Proof using H2 H1.
    intros r AG E1 E2 E8 E9 E18. apply (regs_agree_strengthen _ _ regs r AG).
    intros x Hx Hn. unfold FLBIG in Hx. cbn [In] in Hx.
    destruct Hx as [<-|Hx]; [rewrite E1; symmetry; exact H1|].
    destruct Hx as [<-|Hx]; [rewrite E2; symmetry; exact H2|].
    destruct Hx as [<-|Hx]; [exact E8|].
    destruct Hx as [<-|Hx]; [exact E9|].
    destruct Hx as [<-|Hx]; [exact E18|].
    exfalso. exact (Hn Hx).
  Qed.

  (* [comment removed for export] *)
  Theorem flush_pre : (PBz < PEz)%Z ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 75656) MFL rom)
      /\ getr r 17 = Z_to_bv 64 233 /\ getr r 10 = Z_to_bv 64 PBz /\ getr r 11 = Z_to_bv 64 (PEz - PBz) /\ getr r 12 = Z_to_bv 64 4
      /\ getr r 1 = ra /\ getr r 2 = S
      /\ regs_agree (fun x => In x m2s_clob) regs r.
  Proof using H11 H10 H2 H1 Hstk HS Hcells Hsv Rg_seal Rpgsz Rg_pgsz Hend PH midend Hbase G756ac G113456 MTB MTOK HCI HCR HCF sv g_seal p_pgsz g_pgsz mt.
    intros HLT. destruct flush_head as (r3 & RUN3 & D10 & D2 & D18 & AG3).
    destruct (blkF3 r3 D10 D2 D18 HLT) as (r4 & RUN4 & E17 & E10 & E11 & E12 & E1 & E2 & E8 & E9 & E18 & AG4).
    exists r4. split; [eapply msteps_trans; [exact RUN3 | exact RUN4]|].
    repeat (split; [assumption|]).
    apply fl_clob_final; try assumption.
    eapply regs_agree_trans; [exact AG3 | exact (regs_agree_mono _ _ _ _ FLBIG_sub4 AG4)].
  Qed.

  (* [comment removed for export] *)
  Theorem flush_nocall : (PEz <= PBz)%Z ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra MFL rom)
      /\ getr r 1 = ra /\ getr r 2 = S
      /\ regs_agree (fun x => In x m2s_clob) regs r.
  Proof using H11 H10 H2 H1 Hret Hstk HS Hcells Rpgsz Rg_pgsz Hend PH midend Hbase G113456 MTB MTOK HCR HCF g_seal p_pgsz g_pgsz mt.
    intros HGE. destruct flush_head as (r3 & RUN3 & D10 & D2 & D18 & AG3).
    destruct (blkF3n r3 D10 D2 D18 HGE) as (r4 & RUN4 & E1 & E2 & E8 & E9 & E18 & AG4).
    exists r4. split; [eapply msteps_trans; [exact RUN3 | exact RUN4]|].
    repeat (split; [assumption|]).
    apply fl_clob_final; try assumption.
    eapply regs_agree_trans; [exact AG3 | exact (regs_agree_mono _ _ _ _ FLBIG_sub4 AG4)].
  Qed.
End FLUSH.

(* [comment removed for export] *)
Section FLUSHPOST.
  Variables (segs : list Segment) (base : word).
  Hypothesis HCI : code_ato segs base 75624 imadv_words.
  Lemma Fp_8077c : fetch_word segs (at_ base 75660) = Some W_8077c.   (* [comment removed for export] *)
  Proof using HCI. exact (code_ato_get segs base 75624 imadv_words 9 _ HCI eq_refl). Qed.
  Lemma Fp_80780 : fetch_word segs (at_ base 75664) = Some W_80780.   (* [comment removed for export] *)
  Proof using HCI. exact (code_ato_get segs base 75624 imadv_words 10 _ HCI eq_refl). Qed.

  Theorem flush_post : forall (m5 rom : word -> option byte) (ra : word) r5,
    ret_ok ra -> getr r5 1 = ra -> getr r5 10 = Z_to_bv 64 0 ->
    exists r,
      msteps segs (mkst r5 (at_ base 75660) m5 rom) (mkst r ra m5 rom)
      /\ getr r 10 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [10]%list) r5 r.
  Proof using HCI.
    intros m5 rom ra r5 Hret Q1 Q10.
    wd_eexists. split.
    - an Fp_8077c D_8077c.                                     (* [comment removed for export] *)
      aret Fp_80780 D_80780 ra.                                (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma flush_ecall_fetch : fetch_word segs (at_ base 75656) = Some W_80778.
  Proof using HCI. exact (code_ato_get segs base 75624 imadv_words 8 _ HCI eq_refl). Qed.
End FLUSHPOST.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record flush_tab := FLT { ft_base : word; ft_mt : m2s_tab; ft_g_pgsz : Z; ft_p_pgsz : Z; ft_g_seal : Z; ft_sv : Z }.

Definition flush_tab_ok (segs : list Segment) (t : flush_tab) : Prop :=
  let base := ft_base t in
  code_ato segs base 0 flush_words /\ code_ato segs base 113472 rel_words /\ code_ato segs base 75624 imadv_words
  /\ m2s_tab_ok segs (ft_mt t) /\ mt_base (ft_mt t) = at_ base 76
  /\ gload2 segs base 113496 11 18 (ft_g_pgsz t) /\ gload segs base 75624 13 (ft_g_seal t)
  /\ ((U base mod 2 = 0)%Z /\ (U base + 120000 < 2 ^ 64)%Z)
  /\ (0 < ft_sv t < 2 ^ 64)%Z.

Definition flush_cells (t : flush_tab) : list Z := fl_cells (ft_mt t) (ft_g_pgsz t) (ft_p_pgsz t) (ft_g_seal t).

(* [comment removed for export] *)
Record flushH (segs : list Segment) (t : flush_tab) (mem : word -> option byte) (p size S midend : word) : Prop := FLH {
  fh_m2s : m2sH segs (ft_mt t) mem p midend;
  fh_end : ((0x10007fff8000 <= U p + U size \/ U p + U size <= 0x7fff7fff) /\ U p + U size <= 0x7fffffffffff)%Z;
  fh_g_pgsz : rdn segs mem (Z_to_bv 64 (ft_g_pgsz t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ft_p_pgsz t)));
  fh_pgsz : rdn segs mem (Z_to_bv 64 (ft_p_pgsz t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096));
  fh_g_seal : rdn segs mem (Z_to_bv 64 (ft_g_seal t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ft_sv t)));
  fh_cells : Forall (fun c => 0 <= c /\ c + 8 <= U S - 32)%Z (flush_cells t);
  fh_S : (32 <= U S)%Z;
  fh_stk : store_ok segs mem (at_ S (-32)) 32 = true }.

(* [comment removed for export] *)
Definition fl_pb (p : word) : Z := up4k (fl_sb p).
Definition fl_pe (p size : word) : Z := down4k (fl_se p size).

Lemma fl_geom_t : forall (p size : word),
  ((0x10007fff8000 <= U p + U size \/ U p + U size <= 0x7fff7fff) /\ U p + U size <= 0x7fffffffffff)%Z ->
  (0x7fff8000 <= fl_sb p /\ fl_sb p <= fl_se p size /\ fl_se p size <= 0x10007fff8000 /\ fl_sb p <= fl_pb p /\ fl_pb p <= fl_sb p + 4095
   /\ fl_se p size - 4095 <= fl_pe p size /\ fl_pe p size <= fl_se p size /\ fl_pb p mod 4096 = 0 /\ fl_pe p size mod 4096 = 0 /\ 0 <= fl_pe p size)%Z.
Proof using. intros p size Hend. exact (fl_geom p size Hend). Qed.

Theorem flush_pre_t : forall segs t, flush_tab_ok segs t ->
  forall mem rom (ra S p size midend : word) regs,
  flushH segs t mem p size S midend ->
  getr regs 1 = ra -> getr regs 2 = S -> getr regs 10 = p -> getr regs 11 = size ->
  (fl_pb p < fl_pe p size)%Z ->
  exists r,
    msteps segs (mkst regs (ft_base t) mem rom)
                (mkst r (at_ (ft_base t) 75656) (fl_frame mem S ra (getr regs 8) (getr regs 9) (getr regs 18)) rom)
    /\ getr r 17 = Z_to_bv 64 233 /\ getr r 10 = Z_to_bv 64 (fl_pb p) /\ getr r 11 = Z_to_bv 64 (fl_pe p size - fl_pb p)
    /\ getr r 12 = Z_to_bv 64 4 /\ getr r 1 = ra /\ getr r 2 = S
    /\ regs_agree (fun x => In x m2s_clob) regs r.
Proof using.
  intros segs t TOK mem rom ra S p size midend regs [P1 P2 P3 P4 P5 P6 P7 P8] H1 H2 H10 H11 HLT.
  destruct t as [base mt g_pgsz p_pgsz g_seal sv]; unfold flush_tab_ok, flush_cells, fl_pb, fl_pe in *; cbn [ft_base ft_mt ft_g_pgsz ft_p_pgsz ft_g_seal ft_sv] in *.
  destruct TOK as (C1 & C2 & C3 & MT & MB & G1 & G2 & HB & SV).
  replace (mkst regs base mem rom) with (mkst regs (at_ base 0) mem rom) by (rewrite at_0; reflexivity).
  exact (flush_pre segs base mt g_pgsz p_pgsz g_seal sv C1 C2 C3 MT MB G1 G2 HB mem rom ra S p size midend P1 P2 P3 P4 P5 SV P6 P7 P8 regs H1 H2 H10 H11 HLT).
Qed.

Theorem flush_nocall_t : forall segs t, flush_tab_ok segs t ->
  forall mem rom (ra S p size midend : word) regs,
  flushH segs t mem p size S midend -> ret_ok ra ->
  getr regs 1 = ra -> getr regs 2 = S -> getr regs 10 = p -> getr regs 11 = size ->
  (fl_pe p size <= fl_pb p)%Z ->
  exists r,
    msteps segs (mkst regs (ft_base t) mem rom)
                (mkst r ra (fl_frame mem S ra (getr regs 8) (getr regs 9) (getr regs 18)) rom)
    /\ getr r 1 = ra /\ getr r 2 = S
    /\ regs_agree (fun x => In x m2s_clob) regs r.
Proof using.
  intros segs t TOK mem rom ra S p size midend regs [P1 P2 P3 P4 P5 P6 P7 P8] Hret H1 H2 H10 H11 HGE.
  destruct t as [base mt g_pgsz p_pgsz g_seal sv]; unfold flush_tab_ok, flush_cells, fl_pb, fl_pe in *; cbn [ft_base ft_mt ft_g_pgsz ft_p_pgsz ft_g_seal ft_sv] in *.
  destruct TOK as (C1 & C2 & C3 & MT & MB & G1 & G2 & HB & SV).
  replace (mkst regs base mem rom) with (mkst regs (at_ base 0) mem rom) by (rewrite at_0; reflexivity).
  exact (flush_nocall segs base mt g_pgsz p_pgsz g_seal C1 C2 MT MB G1 HB mem rom ra S p size midend P1 P2 P3 P4 P6 P7 P8 Hret regs H1 H2 H10 H11 HGE).
Qed.

Theorem flush_post_t : forall segs t, flush_tab_ok segs t ->
  forall (m5 rom : word -> option byte) (ra : word) r5,
  ret_ok ra -> getr r5 1 = ra -> getr r5 10 = Z_to_bv 64 0 ->
  exists r,
    msteps segs (mkst r5 (at_ (ft_base t) 75660) m5 rom) (mkst r ra m5 rom)
    /\ getr r 10 = Z_to_bv 64 0
    /\ regs_agree (fun x => In x [10]%list) r5 r.
Proof using.
  intros segs t TOK. destruct TOK as (_ & _ & C3 & _). exact (flush_post segs (ft_base t) C3).
Qed.
Lemma flush_ecall_fetch_t : forall segs t, flush_tab_ok segs t -> fetch_word segs (at_ (ft_base t) 75656) = Some W_80778.
Proof using. intros segs t TOK. destruct TOK as (_ & _ & C3 & _). exact (flush_ecall_fetch segs (ft_base t) C3). Qed.

(* [comment removed for export] *)
Lemma flushH_mrestrict : forall segs t (Hd : word -> bool) mem (p size S midend : word),
  flushH segs t mem p size S midend ->
  Forall (fun c => hid_off Hd c 8) (flush_cells t) -> hid_off Hd (U S - 32) 32 ->
  flushH segs t (mrestrict Hd mem) p size S midend.
Proof using.
  intros segs t Hd mem p size S midend [P1 P2 P3 P4 P5 P6 P7 P8] HC HSC. pose proof (u64_range S) as HSr.
  pose proof P6 as P6'. pose proof HC as HC'. unfold flush_cells, fl_cells, m2s_cells in P6', HC'. cbn [app] in P6', HC'.
  repeat match type of P6' with Forall _ (_ :: _) => apply Forall_cons_iff in P6'; destruct P6' as [? P6'] end.
  repeat match type of HC' with Forall _ (_ :: _) => apply Forall_cons_iff in HC'; destruct HC' as [? HC'] end.
  destruct P1 as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
  assert (RR : forall c v, (0 <= c /\ c + 8 <= U S - 32)%Z -> hid_off Hd c 8 ->
               rdn segs mem (Z_to_bv 64 c) 8 = Some v -> rdn segs (mrestrict Hd mem) (Z_to_bv 64 c) 8 = Some v).
  { intros c v Hc Hh Hr. rewrite rdn_mrestrict; [exact Hr | wd_ulia_c | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); exact Hh]. }
  constructor; try assumption.
  - constructor; try assumption; apply RR; assumption.
  - apply RR; assumption.
  - apply RR; assumption.
  - apply RR; assumption.
  - rewrite store_ok_mrestrict; [exact P8 | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HSC].
Qed.
End FPGen1.
