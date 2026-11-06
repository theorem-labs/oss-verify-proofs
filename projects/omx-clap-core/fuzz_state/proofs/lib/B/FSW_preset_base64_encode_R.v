(* preset_base64_encode 0x84700 (preset_file.c:577-608) on fs.asan-ubsan (image B), the INVARIANT LAYER of the walk
   (Section R up to the 3-byte loop) and the terminating 0 + epilogue (encR_nul, B 0x84b24 .. the ret at 0x84b54), proved
   toward lib/B/FSH_Fn_writer.v's encode_spec. Same names and argument order as image A's Section R
   (lib/A/FSW_preset_base64_encode.v); every numeral here is B's.

   What it proves: the output block's extent facts (encR_size_pos, encR_out_facts, encR_band/img/high_not_out), the output
   and input windows at any walk state (encR_ra_out, encR_wr_out, encR_ra_in), the two blocks' disjointness
   (encR_in_out, encR_new_block, encR_dj, encR_dj_in_tab, encR_dj_out_tab, encR_img_not_in, encR_in_apart), the walk's
   invariant (encR_agree / encR_J / encR_inv) and what it keeps (encR_mb, encR_val, encR_stat_keep, encR_glob_keep,
   encR_tab_keep, encR_hi_keep, encR_ra_keep, encR_in_byte), B's six saved cells (encR_extra / encR_cs / encR_expect /
   encR_chunks), the call's post (encR_Q), the table-seat shent (encR_shent_seat, enc_shseat), the model's prefix step
   (enc_firstn3, encR_prefix_step) and byte-array facts (encR_garr8_app4, encR_garr8_keep), and encR_nul: from B 0x84b24
   (a1 = q + enc_size len - 1) the shadow check of a1, `sb zero,0(a1)` at 0x84b34, the reload of ra / s0 / s1 / s2 / s3 /
   s4 from the 48-byte frame (0x84b38 .. 0x84b4c), `addi sp,sp,48`, `ret` (0x84b54) to encode_spec's success post.
   The inline ASan check of the NUL store (0x84b24 .. 0x84b30, slow path 0x84b5c .. 0x84b68) falls through (the token run);
   no UBSan decider (branch to 0x84b58) lies in 0x84b24 .. 0x84b54.
   Left to the round lane (stated over A's loop-round register atoms 11 / 12 / 17 / 36..38, which B's round does not
   use: B's round reads its input through t4 = a7 + a5, stores through t3 / t6, checks the output through a1):
   encR_extra3, encR_loop_regs, encR_exit_regs, encR_round_state, encR_round_env, encR_seat_dj, encR_seat_ok,
   encR_wr_bound, encR_sh0 and the Ltac enc_shbase.

   rule 24: proves function preset_base64_encode (part R; reuse search: proof-index preset_base64_encode,
   ported from a working branch 402eb5565fc + donor a working branch b96980d72d1)
   Port-from: lib/A/FSW_preset_base64_encode.v at 402eb5565fc lines 741-1232 (Section R head, invariant layer, encR_nul),
   1238-1240 (encR_kept), 1248-1297, 1369-1374, 1439-1460, 1477-1487, 1501-1507, 1515-1570; image-B facts from the old-B
   donor a working branch b96980d72d1 lib/B/Prog/preset_base64_encode_blocks.v:86 (carve_frame 48: the 48-byte
   frame), :105-129 (enc_epilogue: the six reloads 40/32/24/16/8/0(sp), addi sp,sp,48, ret from 0x84b38), :1053-1091
   (enc_finish: the NUL store's block at 0x84b24 = BT 543524). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_preset_base64_encode_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_rres FSW_ret FSW_writer_tbl
FSW_preset_base64_encode_W.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair (lib/B/FSH_Base.v FsShadowSyms) and the image facts (lib/B/FSH_Rt.v fs_img_facts), as in
   lib/B/FSW_preset_base64_encode_W.v's Section W *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* the image layer of lib/B/FSW_preset_base64_encode_W.v at this section's B / HSS / IMG. After its `End W.` each of
   its lemmas takes B and whichever of HSS / IMG its proof uses; each local copy below applies the lemma to the ones it
   takes, so the text of Section R is A's (where Section R sits inside Section W) and survives a change of a W proof. *)
Local Ltac encW X := first [exact (X B HSS IMG) | exact (X B IMG) | exact (X B HSS) | exact (X B) | exact X].
Let enc_blk_bounds := ltac:(encW FSW_preset_base64_encode_W.enc_blk_bounds).
Let enc_blk_not_img := ltac:(encW FSW_preset_base64_encode_W.enc_blk_not_img).
Let enc_ra_block := ltac:(encW FSW_preset_base64_encode_W.enc_ra_block).
Let enc_blk_present := ltac:(encW FSW_preset_base64_encode_W.enc_blk_present).
Let enc_img_rng := ltac:(encW FSW_preset_base64_encode_W.enc_img_rng).
Let enc_ra_agree := ltac:(encW FSW_preset_base64_encode_W.enc_ra_agree).
Let enc_she := ltac:(encW FSW_preset_base64_encode_W.enc_she).
Let enc_frame_X := ltac:(encW FSW_preset_base64_encode_W.enc_frame_X).

(* ---------------------------------------------------------------------------------------------------------- *)
Section R.
Variable ly0 : alayout.  Variable St0 : astate.  Variable U0 : list (Z * Z).
Variable W0 : world tfibsegs.  Variable mem0 : word -> option byte.  Variable md0 : Model.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.  Variable Sc : astate.  Variable Wc : world tfibsegs.
Variable memc : word -> option byte.  Variable mdc : Model.
Variable data len q live peak cnt fail kd : Z.
Variable bs : list Z.

Hypothesis HLN : 0 <= len <= 2 ^ 27.
Hypothesis HBS : WriterSpec.bytes_ok bs.
Hypothesis HBSL : Z.of_nat (length bs) = len.
Hypothesis HDLO : 4096 <= data.
Hypothesis HDHI : data + len <= alloc_ceiling.
(* the state after the call *)
Hypothesis HARUc : ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc memc mdc.
Hypothesis HHEADS : fs_heads B lyc Sc (U0 ++ [(q - HEAD, HEAD)]).
Hypothesis HQB : In (q - HEAD, enc_size len + HEAD) (ablocks B lyc Sc).
Hypothesis HAB : ablocks B lyc Sc = ablocks B ly0 St0 ++ [(q - HEAD, enc_size len + HEAD)].
Hypothesis HQ16 : 4096 + HEAD <= q.
(* the input block, when there is one: an ENTRY block, so the call's new block is a different entry of the list *)
Hypothesis HDB : 0 < len -> In (data - HEAD, kd + HEAD) (ablocks B ly0 St0) /\ len <= kd /\ 0 < kd.

Definition encR_out (a : Z) : Prop := q <= a < q + enc_size len.

Lemma encR_size_pos : 1 <= enc_size len <= 2 ^ 28.
Proof.
unfold enc_size. pose proof (Z.div_le_mono 0 (len + 2) 3 ltac:(lia) ltac:(lia)) as H1.
pose proof (Z.div_le_mono (len + 2) (2 ^ 27 + 2) 3 ltac:(lia) ltac:(lia)) as H2.
change (0 / 3) with 0 in H1. lia.
Qed.

(* the output block's extent: apart from the band, below the ceiling, never an image byte *)
Lemma encR_out_facts :
  enc_apart q (q + enc_size len) /\ q + enc_size len <= alloc_ceiling /\
  (forall a, encR_out a -> ~ in_img tfibsegs a).
Proof.
pose proof encR_size_pos as HM.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
assert (Hrq : req_size (enc_size len + HEAD) = enc_size len + HEAD)
  by (unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
destruct (al_blocks tfibsegs B LAWS lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc _ _ HAR HQB)
  as (_ & _ & Hceil & _).
rewrite Hrq in Hceil.
split; [|split].
- intros x Hx.
  destruct (enc_blk_bounds lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc _ _ x HAR HQB
    ltac:(rewrite Hrq; unfold HEAD in *; lia)) as (_ & _ & A3). exact A3.
- unfold HEAD in *. lia.
- intros a Ha. unfold encR_out in Ha.
  exact (enc_blk_not_img lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc _ _ a HAR HQB
    ltac:(rewrite Hrq; unfold HEAD in *; lia)).
Qed.

Lemma encR_band_not_out : forall i, SHADOW_OFF <= i < SHADOW_OFF + 17592186044416 -> ~ encR_out i.
Proof. intros i Hi Hout. exact (proj1 encR_out_facts i Hout Hi). Qed.
Lemma encR_img_not_out : forall a, in_img tfibsegs a -> ~ encR_out a.
Proof. intros a Ha Hout. exact (proj2 (proj2 encR_out_facts) a Hout Ha). Qed.
Lemma encR_high_not_out : forall a, alloc_ceiling <= a -> ~ encR_out a.
Proof. intros a Ha Hout. pose proof (proj1 (proj2 encR_out_facts)). unfold encR_out in Hout. lia. Qed.

(* the output window at any state of the walk: addressable, present and writable *)
Lemma encR_ra_out : forall mem md, ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md ->
  range_addressable (aview tfibsegs (w_H Wc) mem) SHADOW_OFF q (enc_size len).
Proof.
intros mem md HARU. pose proof encR_size_pos as HM.
exact (enc_ra_block lyc Sc _ Wc mem md q (enc_size len) q (enc_size len) HARU HHEADS HQB ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma encR_wr_out : forall mem md, ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md ->
  forall o, 0 <= o < enc_size len -> writable_at tfibsegs (mrestrict (w_H Wc) mem) (q + o).
Proof.
intros mem md HARU o Ho. pose proof encR_size_pos as HM.
assert (Hrq : req_size (enc_size len + HEAD) = enc_size len + HEAD)
  by (unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
exact (proj2 (enc_blk_present lyc Sc _ Wc mem md (q - HEAD) (enc_size len + HEAD) (q + o) HARU HQB
  ltac:(rewrite Hrq; unfold HEAD in *; lia))).
Qed.

(* the input window at any state of the walk *)
Lemma encR_ra_in : forall mem md, ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md -> 0 < len ->
  range_addressable (aview tfibsegs (w_H Wc) mem) SHADOW_OFF data len.
Proof.
intros mem md HARU Hlen. destruct (HDB Hlen) as (Hin & Hkd & Hkd0).
exact (enc_ra_block lyc Sc _ Wc mem md data kd data len HARU HHEADS
  ltac:(rewrite HAB; apply in_or_app; left; exact Hin) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* the input block and the output block are two entries of AR's pairwise-disjoint block list *)
Lemma encR_in_out : 0 < len -> forall i, data <= i < data + len -> ~ encR_out i.
Proof.
intros Hlen i Hi Hout. unfold encR_out in Hout. destruct (HDB Hlen) as (Hin & Hkd & Hkd0).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
pose proof encR_size_pos as HM.
destruct (al_sep tfibsegs B LAWS lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc HAR) as (Hpw & _).
destruct (in_split _ _ Hin) as (l1 & l2 & Hsp).
set (fb := fun b : Z * Z => (fst b, req_size (snd b))) in *.
set (ff := fun fr : Z * Z => (frame_addr lyc (fst fr) (snd fr), fs_frame_bytes (fst fr))) in *.
assert (Hl : map fb (ablocks B lyc Sc) ++ map ff (frames Sc)
           = map fb l1 ++ fb (data - HEAD, kd + HEAD) ::
             (map fb l2 ++ fb (q - HEAD, enc_size len + HEAD) :: map ff (frames Sc)))
  by (rewrite HAB, Hsp, !map_app, <- !app_assoc; cbn [map app]; reflexivity).
pose proof (YCbq.pairwise_In2 zdisjoint _ (fb (data - HEAD, kd + HEAD)) (fb (q - HEAD, enc_size len + HEAD))
  (map fb l1) (map fb l2) (map ff (frames Sc)) Hpw Hl) as Hdj.
unfold zdisjoint, fb in Hdj. cbn [fst snd] in Hdj.
assert (Hrq : forall n, 0 < n -> req_size (n + HEAD) = n + HEAD)
  by (intros n Hn; unfold req_size; destruct (n + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
rewrite (Hrq kd ltac:(lia)), (Hrq (enc_size len) ltac:(lia)) in Hdj.
unfold HEAD in *. lia.
Qed.

(* the call's new block is NOT one of the entry blocks: the list would hold it twice, against AR's pairwise
   disjointness (a block of at least HEAD bytes is not disjoint from itself) *)
Lemma encR_new_block : ~ In (q - HEAD, enc_size len + HEAD) (ablocks B ly0 St0).
Proof.
intros Hin. pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof encR_size_pos as HM.
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
destruct (al_sep tfibsegs B LAWS lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc HAR) as (Hpw & _).
destruct (in_split _ _ Hin) as (l1 & l2 & Hsp).
set (fb := fun b : Z * Z => (fst b, req_size (snd b))) in *.
set (ff := fun fr : Z * Z => (frame_addr lyc (fst fr) (snd fr), fs_frame_bytes (fst fr))) in *.
assert (Hl : map fb (ablocks B lyc Sc) ++ map ff (frames Sc)
           = map fb l1 ++ fb (q - HEAD, enc_size len + HEAD) ::
             (map fb l2 ++ fb (q - HEAD, enc_size len + HEAD) :: map ff (frames Sc)))
  by (rewrite HAB, Hsp, !map_app, <- !app_assoc; cbn [map app]; reflexivity).
pose proof (YCbq.pairwise_In2 zdisjoint _ (fb (q - HEAD, enc_size len + HEAD))
  (fb (q - HEAD, enc_size len + HEAD)) (map fb l1) (map fb l2) (map ff (frames Sc)) Hpw Hl) as Hdj.
unfold zdisjoint, fb in Hdj. cbn [fst snd] in Hdj.
assert (Hrq : req_size (enc_size len + HEAD) = enc_size len + HEAD)
  by (unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
rewrite Hrq in Hdj. unfold HEAD in *. lia.
Qed.

(* ---- the walk's invariant after the call: the journal over the unpoisoned memories, ARU, and AGREEMENT with
   the call's memory everywhere but the output block ---- *)
Definition encR_agree (mem : word -> option byte) : Prop :=
  forall x : word, ~ encR_out (bv_unsigned x) -> mem x = memc x.
Definition encR_J (mem : word -> option byte) (md : Model) : Prop :=
  ajournal tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP ly0 St0 W0 (unpoison U0 mem0) md0 []
    lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) mem) md EV_preset_base64_encode.
Definition encR_inv (mem : word -> option byte) (md : Model) : Prop :=
  encR_J mem md /\ ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md /\ encR_agree mem.

Lemma encR_mb : forall mem a, encR_agree mem -> ~ encR_out a -> 0 <= a < 2 ^ 64 ->
  mbyte tfibsegs (mrestrict (w_H Wc) mem) a = mbyte tfibsegs (mrestrict (w_H Wc) memc) a.
Proof.
intros mem a HA Ha Hr. unfold mbyte, mrestrict.
rewrite (HA (Z_to_bv 64 a) ltac:(rewrite (wz a Hr); exact Ha)). reflexivity.
Qed.

Lemma encR_val : forall mem a (n : nat) v, encR_agree mem -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> ~ encR_out i) ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) a n v -> val_mem tfibsegs (mrestrict (w_H Wc) mem) a n v.
Proof.
intros mem a n v HA Ha Han HX HV k Hk.
rewrite (encR_mb mem (a + Z.of_nat k) HA (HX (a + Z.of_nat k) ltac:(lia)) ltac:(lia)). exact (HV k Hk).
Qed.

(* the four allocator statics and the table are image bytes, so the walk never writes them *)
Lemma encR_stat_keep : forall mem a (n : nat) v, encR_agree mem ->
  65536 <= a -> a + Z.of_nat n <= 6279168 ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) a n v -> val_mem tfibsegs (mrestrict (w_H Wc) mem) a n v.
Proof.
intros mem a n v HA Hlo Hhi HV.
apply (encR_val mem a n v HA ltac:(lia) ltac:(lia)); [|exact HV].
intros i Hi. apply encR_img_not_out. apply enc_img_rng. lia.
Qed.

Lemma encR_glob_keep : forall mem l p c f, encR_agree mem ->
  fs_glob tfibsegs Wc memc l p c f -> fs_glob tfibsegs Wc mem l p c f.
Proof.
intros mem l p c f HA (G1 & G2 & G3 & G4 & Hr).
unfold fs_glob, fs_glob_at, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply (encR_stat_keep mem _ 8%nat); [exact HA | lia | cbn [Z.of_nat]; lia | exact G1]|].
split; [apply (encR_stat_keep mem _ 8%nat); [exact HA | lia | cbn [Z.of_nat]; lia | exact G2]|].
split; [apply (encR_stat_keep mem _ 8%nat); [exact HA | lia | cbn [Z.of_nat]; lia | exact G3]|].
split; [apply (encR_stat_keep mem _ 8%nat); [exact HA | lia | cbn [Z.of_nat]; lia | exact G4] | exact Hr].
Qed.

Lemma encR_tab_keep : forall mem, encR_agree mem ->
  (forall v, 0 <= v < 64 -> val_mem tfibsegs (mrestrict (w_H Wc) memc) (G_B64 + v) 1 (WriterSpec.b64c v)) ->
  forall v, 0 <= v < 64 -> val_mem tfibsegs (mrestrict (w_H Wc) mem) (G_B64 + v) 1 (WriterSpec.b64c v).
Proof.
intros mem HA HT v Hv.
apply (encR_stat_keep mem (G_B64 + v) 1%nat); [exact HA | unfold G_B64; lia | unfold G_B64; cbn [Z.of_nat]; lia
  | exact (HT v Hv)].
Qed.

(* a stack byte is never an output byte *)
Lemma encR_hi_keep : forall mem a (n : nat) v, encR_agree mem -> alloc_ceiling <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) a n v -> val_mem tfibsegs (mrestrict (w_H Wc) mem) a n v.
Proof.
intros mem a n v HA Hlo Hhi HV.
apply (encR_val mem a n v HA ltac:(pose proof alloc_ceiling_val as (CR & _); lia) ltac:(lia)); [|exact HV].
intros i Hi. apply encR_high_not_out. lia.
Qed.

(* the shadow of a range outside the output block, and of the output block itself, at an invariant memory *)
Lemma encR_ra_keep : forall mem a n, encR_agree mem -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF a n ->
  range_addressable (aview tfibsegs (w_H Wc) mem) SHADOW_OFF a n.
Proof.
intros mem a n HA Ha Han HRA.
exact (enc_ra_agree (w_H Wc) memc mem encR_out a n HA Ha Han encR_band_not_out HRA).
Qed.

(* ---- what the call's entry memory holds (the fuzz_malloc call's post, read at memc) ---- *)
Hypothesis HRBc : fs_rblock tfibsegs B lyc Sc Wc memc q (enc_size len).
Hypothesis HGLOBc : fs_glob tfibsegs Wc memc (live + enc_size len) (Z.max peak (live + enc_size len))
  ((cnt + 1) mod 2 ^ 64) fail.
Hypothesis HTABc : forall v, 0 <= v < 64 ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (G_B64 + v) 1 (WriterSpec.b64c v).
Hypothesis HRATc : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF G_B64 65.
Hypothesis HDATc : garr8 tfibsegs (mrestrict (w_H Wc) memc) data bs.
Hypothesis HKEEPc : forall i, 0 <= i < len ->
  mbyte tfibsegs (mrestrict (w_H Wc) memc) (data + i) = mbyte tfibsegs (mrestrict (w_H W0) mem0) (data + i).
(* the entry frame: ra, s0, s1, s2, s3, s4 saved by the prologue (0x84704 .. 0x84718: sd ra,40(sp) .. sd s4,0(sp) after
   addi sp,sp,-48), still there after the call *)
Hypothesis HFRAMEc :
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 48) 8 (bv_unsigned (getr regs0 20)).
Hypothesis HSP0 : spZ regs0 mod 16 = 0 /\ alloc_ceiling + STK_preset_base64_encode <= spZ regs0 /\
  spZ regs0 <= 2 ^ 47.
Hypothesis HRA0 : YK0s.ret_ok (getr regs0 1).

(* the six saved registers of the entry, as the resumed states' extra atoms 32 .. 37 *)
Definition encR_extra : list word :=
  [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20].
Definition encR_cs : list YP09.chunk :=
  [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0));
   YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
   YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 0 (CVal 8 (SOff 37 0))].
(* what the callee-saved registers hold at `ret`: sp back up by the frame, s0 / s1 / s2 / s3 / s4 reloaded, the rest
   untouched *)
Definition encR_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 48 | 8 => SOff 33 0 | 9 => SOff 34 0 | 18 => SOff 35 0 | 19 => SOff 36 0 | 20 => SOff 37 0
  | z => SOff (Z.to_nat z) 0
  end.

Lemma encR_chunks : forall mem (regsX : bvmap 5 word), encR_agree mem ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regsX encR_extra) (mrestrict (w_H Wc) mem) (spZ regs0 - 48)) encR_cs.
Proof.
intros mem regsX HA. pose proof HSP0 as (Hal16 & Hceil & H47). pose proof alloc_ceiling_val as (CR & _).
destruct HFRAMEc as (V1 & V8 & V9 & V18 & V19 & V20).
assert (HSTK : STK_preset_base64_encode
  = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v)) by reflexivity.
assert (F : forall (j : nat) (r : bv 5) od, nth j encR_extra (Z_to_bv 64 0) = getr regs0 r ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 48 + od) 8 (bv_unsigned (getr regs0 r)) ->
  0 <= od -> od + 8 <= 48 ->
  YP09.chunk_ok tfibsegs (Ereg regsX encR_extra) (mrestrict (w_H Wc) mem) (spZ regs0 - 48)
    (YP09.mkChunk od (CVal 8 (SOff (32 + j) 0)))).
{ intros j r od Hj Hv Ho1 Ho2.
  apply (chunk_ok_val tfibsegs _ _ _ od 8%N (SOff (32 + j) 0) (bv_unsigned (getr regs0 r)));
    first [ solve [apply u64_range]
          | lazymatch goal with |- sv_denot _ _ = _ =>
              rewrite fsw_SOff0, ew_Ereg_extra, Hj; symmetry; apply Z_to_bv_bv_unsigned end
          | solve [cbn; lia]
          | idtac ].
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
  apply (encR_hi_keep mem (spZ regs0 - 48 + od) 8%nat _ HA); [lia | cbn [Z.of_nat]; lia | exact Hv]. }
unfold encR_cs. repeat constructor.
- apply (F 0%nat 1%bv 40 eq_refl); [replace (spZ regs0 - 48 + 40) with (spZ regs0 - 8) by lia; exact V1 | lia | lia].
- apply (F 1%nat 8%bv 32 eq_refl); [replace (spZ regs0 - 48 + 32) with (spZ regs0 - 16) by lia; exact V8 | lia | lia].
- apply (F 2%nat 9%bv 24 eq_refl); [replace (spZ regs0 - 48 + 24) with (spZ regs0 - 24) by lia; exact V9 | lia | lia].
- apply (F 3%nat 18%bv 16 eq_refl); [replace (spZ regs0 - 48 + 16) with (spZ regs0 - 32) by lia; exact V18 | lia | lia].
- apply (F 4%nat 19%bv 8 eq_refl); [replace (spZ regs0 - 48 + 8) with (spZ regs0 - 40) by lia; exact V19 | lia | lia].
- apply (F 5%nat 20%bv 0 eq_refl); [replace (spZ regs0 - 48 + 0) with (spZ regs0 - 48) by lia; exact V20 | lia | lia].
Qed.

(* the call's post, as encode_spec's success arm states it *)
Definition encR_Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
    getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
    ablocks B ly' S' = ablocks B ly0 St0 ++ [(q - HEAD, enc_size len + HEAD)] /\
    fs_rblock tfibsegs B ly' S' W' mem' q (enc_size len) /\
    zbytes_at tfibsegs W' mem' q (WriterSpec.b64_enc bs ++ [0]) /\
    (forall i, 0 <= i < len -> mbyte tfibsegs (mrestrict (w_H W') mem') (data + i)
                             = mbyte tfibsegs (mrestrict (w_H W0) mem0) (data + i)) /\
    fs_glob tfibsegs W' mem' (live + enc_size len) (Z.max peak (live + enc_size len)) ((cnt + 1) mod 2 ^ 64) fail.

(* ---- the terminating 0 and the epilogue (B 0x84b24 .. the ret at 0x84b54): 0x84b24 .. 0x84b30 the shadow check of
   a1 (slow path 0x84b5c .. 0x84b60 back to 0x84b34), 0x84b34 sb zero,0(a1), 0x84b38 .. 0x84b4c the six reloads,
   0x84b50 addi sp,sp,48, 0x84b54 ret ---- *)
Definition encR_nul_ss : sstate :=
  mkSS 0x84b24 sr_atoms [YP09.mkRegion (Some 11%nat) 0 1 0 1 []; fstk_ret 48 encR_cs] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 PTOP 0);
              (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
Definition encR_nul_SH : list shent := [mkSHE 11 0 1].

Lemma encR_nul : forall ms md,
  encR_inv (ms_mem ms) md ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q (WriterSpec.b64_enc bs) ->
  ms = mkst (ms_regs ms) (w64 0x84b24) (ms_mem ms) (seg_rom tfibsegs) ->
  getr (ms_regs ms) 10 = w64 q ->
  getr (ms_regs ms) 11 = w64 (q + 4 * ((len + 2) / 3)) ->
  getr (ms_regs ms) 18 = w64 SHADOW_OFF ->
  spZ (ms_regs ms) = spZ regs0 - 48 ->
  (forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 -> z <> 19 -> z <> 20 ->
     getr (ms_regs ms) (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z)) ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof.
intros ms md (HJ & HARU & HA) HPRE Hms R10 R11 R18 Rsp Rk.
unfold encR_J in HJ.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof HSP0 as (Hal16 & Hceil & H47).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
assert (HSTK : STK_preset_base64_encode
  = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v)) by reflexivity.
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
assert (Hqn : q + 4 * ((len + 2) / 3) = q + enc_size len - 1) by (unfold enc_size; lia).
assert (E2 : bv_unsigned (ew (Ereg (ms_regs ms) encR_extra) 2) = spZ regs0 - 48)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); exact Rsp).
assert (A11 : ew (Ereg (ms_regs ms) encR_extra) 11 = w64 (q + enc_size len - 1))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl), R11, Hqn; reflexivity).
assert (A18 : ew (Ereg (ms_regs ms) encR_extra) 18 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact R18).
assert (E11 : bv_unsigned (ew (Ereg (ms_regs ms) encR_extra) 11) = q + enc_size len - 1)
  by (rewrite A11; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (E18 : bv_unsigned (ew (Ereg (ms_regs ms) encR_extra) 18) = SHADOW_OFF)
  by (rewrite A18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS : st_ok tfibsegs (Ereg (ms_regs ms) encR_extra) encR_nul_ss (restrict (w_H Wc) ms)).
{ rewrite Hms, restrict_mkst_fx. unfold encR_nul_ss. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E11. split; [lia|]. split; [unfold PTOP; lia|]. split; [|constructor].
      intros o Ho. replace (q + enc_size len - 1 + o) with (q + (enc_size len - 1)) by lia.
      exact (encR_wr_out (ms_mem ms) md HARU (enc_size len - 1) ltac:(lia)).
    + exact (fsw_resume_frame_ok B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP ly0 St0 W0
        (unpoison U0 mem0) md0 [] lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc (ms_mem ms) md
        EV_preset_base64_encode (Ereg (ms_regs ms) encR_extra) 48 encR_cs HJ HARU E2 ltac:(lia)
        (encR_chunks (ms_mem ms) (ms_regs ms) HA)).
  - apply pairwise_disjoint_of_extents.
    unfold fstk_ret, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E11.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I. left. lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E11, E18. change (2 ^ 4) with 16. rewrite !Z.pow_0_r.
    split; [split; [lia | split; [rewrite Zminus_mod, Hal16; reflexivity | lia]]|].
    split; [|split; [|exact I]].
    + split; [unfold PTOP; lia | split; [apply Z.mod_1_r | lia]].
    + split; [lia | split; [apply Z.mod_1_r | lia]]. }
assert (SHOK : sh_ok tfibsegs enc_Bx encR_nul_SH (Ereg (ms_regs ms) encR_extra)
  (mrestrict (w_H Wc) (ms_mem ms))).
{ unfold sh_ok, encR_nul_SH. constructor; [|constructor].
  apply (enc_she Wc (ms_mem ms) (Ereg (ms_regs ms) encR_extra) 11%nat (q + enc_size len - 1) 0 1 q
    (enc_size len)).
  - apply (U_atom _ 18 SHADOW_OFF A18). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 11 _ A11). unfold PTOP in *. lia.
  - exact (encR_ra_out (ms_mem ms) md HARU).
  - lia.
  - lia.
  - lia.
  - intros x Hx. apply HAPq. lia. }
fsw_aj_run_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan.
all: first
  [ solve [ cbn [encR_nul_ss ss_mem];
            eapply awr_ok_cons_gen with (k := 11%nat) (b := q + enc_size len - 1);
            first [ solve [reflexivity] | solve [exact E11]
                  | solve [fsw_awr_ret E2 48]
                  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
                    exists (q - HEAD), (enc_size len + HEAD);
                    split; [exact HQB|]; split; [exact encR_new_block|];
                    unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
                    [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD in *; lia] ] ]
  | idtac ].
(* the run stored the 0 at a1 and read the frame back; the rest of the output block is as the walk left it *)
assert (EX : forall n, (n < 38)%nat ->
  ew (ewset (ewset (Ereg (ms_regs ms) encR_extra) 38 w) 39 w0) n = ew (Ereg (ms_regs ms) encR_extra) n)
  by (intros n Hn; rewrite !ew_ewset_other by lia; reflexivity).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (q + enc_size len - 1 <= a < q + enc_size len) ->
  ~ (spZ regs0 - 48 <= a < spZ regs0) ->
  mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
{ intros a Ha H1 H2. unfold mbyte.
  rewrite (enc_frame_X (Ereg (ms_regs ms) encR_extra) (ss_mem encR_nul_ss)
    (mrestrict (w_H Wc) (ms_mem ms)) (mrestrict (w_H Wc) (ms_mem ms0))
    (fun x => (q + enc_size len - 1 <= x < q + enc_size len) \/ (spZ regs0 - 48 <= x < spZ regs0)) HFr);
    [reflexivity | | rewrite (wz a Ha); intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros x (r & Hin & Hr). cbn [encR_nul_ss ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fstk_ret] in Hr;
    [rewrite E11 in Hr; left; lia | rewrite E2 in Hr; right; lia]. }
assert (VK : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> ~ encR_out i) ->
  (forall i, a <= i < a + Z.of_nat n -> ~ (spZ regs0 - 48 <= i < spZ regs0)) ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) a n v ->
  val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) a n v).
{ intros a n v Ha Han X1 X3 HV k Hk.
  rewrite (KEEP (a + Z.of_nat k) ltac:(lia)
    ltac:(intros Hc; apply (X1 (a + Z.of_nat k) ltac:(lia)); unfold encR_out; lia)
    (X3 (a + Z.of_nat k) ltac:(lia))).
  exact (encR_val (ms_mem ms) a n v HA Ha Han X1 HV k Hk). }
(* the NUL byte the run stored *)
assert (VNUL : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) (q + enc_size len - 1) 1 0).
{ pose proof (fsw_region_nth (ewset (ewset (Ereg (ms_regs ms) encR_extra) 38 w) 39 w0) _
    (restrict (w_H Wc) ms0) 0 (YP09.mkRegion (Some 11%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))])
    HS ltac:(vm_compute; reflexivity)) as HR.
  cbn [ms_mem restrict] in HR.
  replace (q + enc_size len - 1) with (q + enc_size len - 1 + 0) at 1 by lia.
  apply (fsw_field (ewset (ewset (Ereg (ms_regs ms) encR_extra) 38 w) 39 w0) _ 11
    (q + enc_size len - 1) _ 0 1 0 1 0 1%N (SLit 0) 0 HR);
    first [ solve [rewrite EX by lia; exact E11] | solve [cbn; tauto] | solve [reflexivity]
          | solve [cbn [Z.of_N]; lia] ]. }
(* the registers at the ret *)
assert (R1F : getr (ms_regs ms0) 1 = getr regs0 1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms0 1%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  rewrite fsw_SOff0, EX by lia. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (Ra0 : getr (ms_regs ms0) 10 = w64 q).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms0 10%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  rewrite fsw_SOff0, EX by lia. rewrite (ew_Ereg_nat (ms_regs ms) _ 10 10%bv eq_refl). exact R10. }
apply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok Wc _ _ ms0 _ STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP
  regs0 ly0 St0 U0 W0 mem0 md0 lyc Sc (U0 ++ [(q - HEAD, HEAD)]) EV_preset_base64_encode encR_Q HS).
- reflexivity.
- vm_compute. reflexivity.
- rewrite R1F. exact HRA0.
- exact HJ.
- exact HARU.
- (* the callee-saved registers *)
  apply (fsw_preserved _ _ _ ms0 regs0 encR_expect HS ltac:(vm_compute; reflexivity)).
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (encR_expect ?z) = _ =>
    let e := eval vm_compute in (encR_expect z) in change (encR_expect z) with e end;
  first
  [ solve [apply bv_eq; rewrite denot_SOff; rewrite EX by lia; rewrite E2; unfold spZ;
           replace (bv_unsigned (getr regs0 2) - 48 + 48) with (bv_unsigned (getr regs0 2)) by lia;
           apply zcanon_id; unfold M64; apply u64_range]
  | solve [rewrite fsw_SOff0, EX by lia; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity]
  | solve [rewrite fsw_SOff0, EX by lia; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity]
  | solve [rewrite fsw_SOff0, EX by lia; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity]
  | solve [rewrite fsw_SOff0, EX by lia; change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity]
  | solve [rewrite fsw_SOff0, EX by lia; change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity]
  | solve [rewrite fsw_SOff0, EX by lia;
           lazymatch goal with |- ew _ ?n = getr _ ?r =>
             rewrite (ew_Ereg_nat (ms_regs ms) _ n r eq_refl);
             let z := eval vm_compute in (bv_unsigned r) in
             exact (Rk z ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(lia)) end] ].
- (* the post *)
  intros mat2. unfold encR_Q.
  pose proof encR_size_pos as HM2.
  split; [exact Ra0|]. split; [unfold HEAD in *; lia|]. split; [exact HAB|].
  split.
  { destruct HRBc as (Hin & H16 & Hpos & Hhd). split; [exact Hin|]. split; [exact H16|].
    split; [exact Hpos|].
    apply (VK (q - HEAD) 8%nat); first
      [ solve [unfold HEAD in *; lia]
      | solve [intros i Hi; unfold encR_out, HEAD in *; cbn [Z.of_nat] in *; lia]
      | solve [intros i Hi; unfold HEAD in *; cbn [Z.of_nat] in *; lia]
      | solve [exact Hhd] ]. }
  split.
  { (* the output bytes and the terminating 0 *)
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    pose proof (b64_enc_len bs) as HBL. rewrite HBSL in HBL.
    destruct (Nat.lt_ge_cases j (length (WriterSpec.b64_enc bs))) as [Hlt|Hge].
    - rewrite app_nth1 by exact Hlt.
      destruct (HPRE j Hlt) as (HV & HB256). split; [|exact HB256].
      intros k Hk. rewrite (KEEP (q + Z.of_nat j + Z.of_nat k) ltac:(lia) ltac:(lia) ltac:(lia)).
      exact (HV k Hk).
    - assert (Hje : j = length (WriterSpec.b64_enc bs)) by lia.
      subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      split; [|lia].
      replace (q + Z.of_nat (length (WriterSpec.b64_enc bs))) with (q + enc_size len - 1)
        by (unfold enc_size; lia).
      exact VNUL. }
  split.
  { intros i Hi.
    rewrite (KEEP (data + i) ltac:(lia)
      ltac:(intros Hc; apply (encR_in_out ltac:(lia) (data + i) ltac:(lia)); unfold encR_out; lia)
      ltac:(lia)).
    rewrite (encR_mb (ms_mem ms) (data + i) HA ltac:(apply encR_in_out; lia) ltac:(lia)).
    exact (HKEEPc i Hi). }
  { destruct HGLOBc as (G1 & G2 & G3 & G4 & Hr).
    unfold fs_glob, fs_glob_at, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
    assert (VG : forall a v, 65536 <= a -> a + 8 <= 6279168 ->
      val_mem tfibsegs (mrestrict (w_H Wc) memc) a 8 v ->
      val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) a 8 v).
    { intros a v Hlo Hhi HV. apply (VK a 8%nat); first
        [ solve [lia] | solve [cbn [Z.of_nat]; lia]
        | solve [intros i Hi; apply encR_img_not_out; apply enc_img_rng; cbn [Z.of_nat] in *; lia]
        | solve [intros i Hi; cbn [Z.of_nat] in *; lia]
        | solve [exact HV] ]. }
    split; [apply VG; [lia | lia | exact G1]|]. split; [apply VG; [lia | lia | exact G2]|].
    split; [apply VG; [lia | lia | exact G3]|]. split; [apply VG; [lia | lia | exact G4] | exact Hr]. }
Qed.

(* ---- the walk's register facts that hold from the call's return to the ret: the callee-saved registers the
   prologue did not save are the entry's (B saves s3 / s4 too: the loop's shadow checks use s3 (0x84864 .. 0x8486c)
   and the slow paths s3 / s4 (0x84924 .., 0x84960 ..)) ---- *)
Definition encR_kept (ms : machine_state) : Prop :=
  forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 -> z <> 19 -> z <> 20 ->
    getr (ms_regs ms) (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z).

(* the input block and the output block are two intervals that do not meet *)
Lemma encR_dj : 0 < len -> data + len <= q \/ q + enc_size len <= data.
Proof.
intros Hlen. pose proof encR_size_pos as HM.
destruct (Z_le_gt_dec (data + len) q) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (q + enc_size len) data) as [H2|H2]; [right; exact H2|].
exfalso. apply (encR_in_out Hlen (Z.max data q)); [lia|]. unfold encR_out. lia.
Qed.

(* g_b64 is image, the two blocks are not: the table meets neither window *)
Lemma encR_img_not_in : 0 < len -> forall a, in_img tfibsegs a -> ~ (data <= a < data + len).
Proof.
intros Hlen a Ha Hin. destruct (HDB Hlen) as (Hb & Hkd & Hkd0).
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
assert (Hrq : req_size (kd + HEAD) = kd + HEAD)
  by (unfold req_size; destruct (kd + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
apply (enc_blk_not_img lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc (data - HEAD) (kd + HEAD) a HAR
  ltac:(rewrite HAB; apply in_or_app; left; exact Hb) ltac:(rewrite Hrq; unfold HEAD in *; lia)).
exact Ha.
Qed.

Lemma encR_dj_in_tab : 0 < len -> data + len <= G_B64 \/ G_B64 + 65 <= data.
Proof.
intros Hlen.
destruct (Z_le_gt_dec (data + len) G_B64) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (G_B64 + 65) data) as [H2|H2]; [right; exact H2|].
exfalso. apply (encR_img_not_in Hlen (Z.max data G_B64)); [|lia].
apply enc_img_rng. unfold G_B64 in *. lia.
Qed.

Lemma encR_dj_out_tab : q + enc_size len <= G_B64 \/ G_B64 + 65 <= q.
Proof.
pose proof encR_size_pos as HM.
destruct (Z_le_gt_dec (q + enc_size len) G_B64) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (G_B64 + 65) q) as [H2|H2]; [right; exact H2|].
exfalso. apply (encR_img_not_out (Z.max q G_B64)); [|unfold encR_out; lia].
apply enc_img_rng. unfold G_B64 in *. lia.
Qed.

(* the round's three input bytes, read at any invariant memory *)
Lemma encR_in_byte : forall mem (j : nat), encR_agree mem -> (j < length bs)%nat ->
  val_mem tfibsegs (mrestrict (w_H Wc) mem) (data + Z.of_nat j) 1 (nth j bs 0) /\ 0 <= nth j bs 0 < 256.
Proof.
intros mem j HA Hj. pose proof alloc_ceiling_val as (CR & _).
destruct (HDATc j Hj) as (HV & HB). split; [|exact HB].
apply (encR_val mem (data + Z.of_nat j) 1%nat _ HA ltac:(lia) ltac:(cbn [Z.of_nat]; lia));
  [|exact HV].
intros i Hi. apply (encR_in_out ltac:(lia)). cbn [Z.of_nat] in *. lia.
Qed.

Lemma encR_U_of_bv : forall (E : env) n v, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 ->
  U E (SOff n 0) = v.
Proof.
intros E n v H Hv. apply U_atom; [|exact Hv].
apply bv_eq. rewrite H. symmetry. apply unsigned_lit_small. exact Hv.
Qed.

Lemma encR_in_apart : 0 < len -> enc_apart data (data + len).
Proof.
intros Hlen x Hx. destruct (HDB Hlen) as (Hb & Hkd & Hkd0).
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
assert (Hrq : req_size (kd + HEAD) = kd + HEAD)
  by (unfold req_size; destruct (kd + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
destruct (enc_blk_bounds lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc (data - HEAD) (kd + HEAD) x HAR
  ltac:(rewrite HAB; apply in_or_app; left; exact Hb) ltac:(rewrite Hrq; unfold HEAD in *; lia)) as (_ & _ & A3).
exact A3.
Qed.

(* a table seat's shent, at any invariant memory *)
Lemma encR_shent_seat : forall mem (E : env) (n : nat) v, encR_agree mem ->
  U E enc_Bx = SHADOW_OFF -> U E (SOff n 0) = G_B64 + v -> 0 <= v < 64 ->
  shent_ok tfibsegs enc_Bx E (mrestrict (w_H Wc) mem) (mkSHE n 0 1).
Proof.
intros mem E n v HA HB Hn Hv.
apply (enc_she Wc mem E n (G_B64 + v) 0 1 G_B64 65 HB Hn); [|lia | lia | lia|].
- apply (encR_ra_keep mem G_B64 65 HA); [unfold G_B64; lia | unfold G_B64; lia | exact HRATc].
- intros x Hx. unfold G_B64, SHADOW_OFF in *. lia.
Qed.

(* the three bytes a round consumes, as a prefix step *)
Lemma enc_firstn3 : forall (l : list Z) (n : nat), (n + 3 <= length l)%nat ->
  firstn (n + 3) l = firstn n l ++ [nth n l 0; nth (S n) l 0; nth (S (S n)) l 0].
Proof.
intros l n. revert l. induction n as [|n IH]; intros l Hl.
- destruct l as [|a [|b [|c t]]]; cbn [length] in Hl; try lia.
  cbn [firstn nth app]. reflexivity.
- destruct l as [|a t]; cbn [length] in Hl; [lia|].
  replace (S n + 3)%nat with (S (n + 3)) by lia.
  cbn [firstn]. rewrite (IH t ltac:(lia)). cbn [nth app]. reflexivity.
Qed.

(* a table seat's shent at a state whose env reads the shadow base s2 (A18x) and holds the seat on atom n *)
Ltac enc_shseat memx HAx n idx A18x :=
  apply (encR_shent_seat memx _ n idx HAx);
  first [ solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia); rewrite A18x;
                   apply unsigned_lit_small; unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia]]
        | solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same;
                   apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia]]
        | solve [lia] ].

(* the model step of one round, and the two list facts the walk needs of it *)
Lemma encR_prefix_step : forall r b0 b1 b2, 0 <= r -> 3 * r + 3 <= len ->
  nth (Z.to_nat (3 * r)) bs 0 = b0 -> nth (Z.to_nat (3 * r + 1)) bs 0 = b1 ->
  nth (Z.to_nat (3 * r + 2)) bs 0 = b2 ->
  WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs)
  = WriterSpec.b64_enc (firstn (Z.to_nat (3 * r)) bs)
    ++ [WriterSpec.b64c (b0 / 4); WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16);
        WriterSpec.b64c ((b1 mod 16) * 4 + b2 / 64); WriterSpec.b64c (b2 mod 64)]
  /\ Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * r)) bs))) = 4 * r.
Proof.
intros r b0 b1 b2 Hr Hr3 N0 N1 N2.
assert (HLP : length (firstn (Z.to_nat (3 * r)) bs) = (3 * Z.to_nat r)%nat)
  by (rewrite length_firstn; lia).
split; [|rewrite b64_enc_len, HLP; lia].
assert (HFI : firstn (Z.to_nat (3 * (r + 1))) bs = firstn (Z.to_nat (3 * r)) bs ++ [b0; b1; b2]).
{ replace (Z.to_nat (3 * (r + 1))) with (Z.to_nat (3 * r) + 3)%nat by lia.
  rewrite (enc_firstn3 bs (Z.to_nat (3 * r)) ltac:(lia)).
  rewrite N0. replace (S (Z.to_nat (3 * r))) with (Z.to_nat (3 * r + 1)) by lia.
  rewrite N1. replace (S (Z.to_nat (3 * r + 1))) with (Z.to_nat (3 * r + 2)) by lia.
  rewrite N2. reflexivity. }
rewrite HFI, (b64_enc_app (Z.to_nat r) _ _ HLP), (b64_enc_3 b0 b1 b2 []).
cbn [WriterSpec.b64_enc]. rewrite app_nil_r. reflexivity.
Qed.

(* four bytes appended to a byte array *)
Lemma encR_garr8_app4 : forall (m : word -> option byte) (pre : list Z) (c0 c1 c2 c3 base off : Z),
  garr8 tfibsegs m base pre -> Z.of_nat (length pre) = off -> 0 <= base -> base + off + 4 <= 2 ^ 64 ->
  val_mem tfibsegs m (base + off + 0) 1 c0 -> val_mem tfibsegs m (base + off + 1) 1 c1 ->
  val_mem tfibsegs m (base + off + 2) 1 c2 -> val_mem tfibsegs m (base + off + 3) 1 c3 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  garr8 tfibsegs m base (pre ++ [c0; c1; c2; c3]).
Proof.
intros m pre c0 c1 c2 c3 base off HP Hoff Hb Hb4 V0 V1 V2 V3 R0 R1 R2 R3 j Hj.
rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length pre)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt. exact (HP j Hlt).
- rewrite app_nth2 by exact Hge.
  destruct (j - length pre)%nat as [|[|[|[|k]]]] eqn:Ek; [| | | | lia]; cbn [nth];
    (split; [|lia]);
    [ replace (base + Z.of_nat j) with (base + off + 0) by lia; exact V0
    | replace (base + Z.of_nat j) with (base + off + 1) by lia; exact V1
    | replace (base + Z.of_nat j) with (base + off + 2) by lia; exact V2
    | replace (base + Z.of_nat j) with (base + off + 3) by lia; exact V3 ].
Qed.

(* a byte array survives a keep *)
Lemma encR_garr8_keep : forall (m m' : word -> option byte) (base : Z) (l : list Z) (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  0 <= base -> base + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, base <= i < base + Z.of_nat (length l) -> ~ X i) ->
  garr8 tfibsegs m base l -> garr8 tfibsegs m' base l.
Proof.
intros m m' base l X HK Hb Hbl HX HP j Hj. destruct (HP j Hj) as (HV & HB). split; [|exact HB].
intros k Hk. rewrite (HK (base + Z.of_nat j + Z.of_nat k) ltac:(lia) ltac:(apply HX; lia)).
exact (HV k Hk).
Qed.
End R.

End W.
