(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumD.v, with its module paths and module names changed; 1378 of its 1493 lines of code are new or changed and 601 lines of the source are left out. *)
(* fuzz_preset, slice S5b, lane WalkNumEnd (worker a Theorem Labs lane, for a Theorem Labs lane): parse_value's NUMBER ARM, its LAST
   SEGMENT in image A - listing rows 299..328 of the neutral per-function listing of the pinned rebuilt image A
   (the internal file neutral_dis.py omx-clap-core-preset-ranout/asan/fuzz_preset parse_value; image sha256 d83eb25dbf0df6d5...,
   objdump sha256 3d8143a4cdf95d11...; row 1 is the entry 0x85f10, row n is Listing_prog slot n + 4682, listing v4).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).

   THE ROWS (A 0x863b4..0x86428):
   - rows 299..303: a1 = v + 8 and the shadow byte of v + 8 (through s7; 0: the node's addressable bytes);
   - row 304: a0 = *endptr = res + cc (s9 = fr + 32, the endptr cell strtod wrote);
   - row 305 `fsd fa0, 0(a1)`: the double into the node's num word. ONE HAND STEP: the symbolic runner has no F
     instruction, so the run stops there (PTS_stopped) and the step is YSRrMemnorm.SRr_step_inv (YA0n.SRr_step with
     the invariant) with YK0o.fp_step_fsd, its journal step YCbqG.ajournal_x_exec_fr (write premise: the node's first
     16 bytes, the boundary's own conjunct);
   - rows 306..311: the shadow byte of res + cc (a partial granule: the slow path at rows 343..344 passes) and the byte
     at res + cc; non-zero -> row 326 (the token was not consumed whole);
   - row 312 `fclass.d a0, fa0`: ONE HAND STEP, SRr_step_inv with YFclsStep.fp_step_fclass_d (a Theorem Labs lane's 04:33Z
     ruling: no second fclass step lemma); rows 313..315: the class mask 0x381 (infinities, NaNs) -> row 326;
   - rows 316..325: the shadow of v (4 bytes, the slow path at rows 348..350 passes), tag 3 at v, the shadow of q
     (through s11), s5 = 0, q->p = s6;
   - rows 326..328: VrdRefJoinP.vrd_ref_join_P (both exits pass it), at strtod's float state fx2.
   Every run is a P twin: YC80xf_inv.paj_run_xf_inv / paj_run_to_xf_inv (rows 299..326) and YSRrMemnorm.paj_run_to_x_inv
   inside vrd_ref_join_P (rows 326..328). Rows 299..328 make no call.
   THE ENTRY is VnumF's boundary vrd_num299_a (lib/A/VrdNumTail.v, a working branch c27f0ef31e6, taken by merge).
   THE CONCLUSION, vrd_num_end_stmt (the form VnumF / VnumG's vrd_num_tail binds): the shared join at row 225
   (VrdNum.vrd_epi_a with the entry float state pinned (fx := fx), the arm's result VrdNum.vrd_pv_post) AND the memory
   invariant P at the join, from P at row 299. GENERIC in P with its laws srr_inv_laws (YSRrMemnorm.v), a Theorem Labs lane's
   12:18Z template: an SRr post is opaque once Qed, so an end-state invariant must be in the segment's statement; P is
   instantiated once at the function's top (the memnorm keep, srr_inv_laws_imp / srr_inv_laws_memnorm_k). Call-free:
   no srr_inv_call, no srr_inv_mn.
   WHICH CHANGE MOVED A STATEMENT: the INVARIANT only. vne_seg_299 (pushed Qed at preset-tree-at-2026-10-29T11-46-29Z.tsv (sha256 40aa26e3e2c9; internal record)) is now vne_seg_299_P
   (P premise, P in both continuations); the old statement survives BYTE-IDENTICAL as its P := fun _ => True corollary
   (Section mt). No premise moved for a callee's text. Nothing outside this file cites vne_seg_299.
   THEOREM vrd_num_end : vrd_num_end_stmt. SECTION HYPOTHESES (Section e): LAWS (the engine's laws), HW
   (PRH_Base.prh_head_wide, 8 <= cf_head: a harness head word lies apart from the node; a Theorem Labs lane's preset_head_wide,
   lib/A/CfParamsPreset.v:95, discharges it), H_pst_img (alloc.c's statics are image bytes: S1ImgA.pst_in_img_A).
   FILES TAKEN BY PATH: lib/Reusable/YAkMemnorm.v (blob 96c72061b4d4) and YSRrMemnorm.v (blob a1c1ece77b14) from
   a working branch a7b940285d0 / 161f89a71b4d; YC80xf_inv.v (blob 082f0c430210) from a working branch
   1941d76deca. Cited: VrdRefJoinP.vrd_ref_join_P (this branch, 3227e8d9d8a), VrdLedgerEv.vle_alloc (the S3 walk).
   BUILD SET: a working branch c27f0ef31e6 (base b2db994e5ff: record texts ee649e1b39d on walkkit-next 2d523216ac5
   preview, vpro 4d24e888b31, ielem 6372b90e841) + a working branch 6b77d4d5bc9 + a working branch
   preset-tree-at-2026-10-29T09-43-08Z.tsv (sha256 cbbadb85ecdb; internal record) (its VrdCallKeep.v reset to the vnumt copy). Numerals: the listing rows (LENGTH: slot offsets via
   vrd_row), 8 16 24 56 64 (LENGTH: the node's words, the class-0 frame), 104 (LENGTH: the 13 saved words), 224 512
   (LENGTH: the texts' peak bounds), 897 1024 2047 52 (WORD / LENGTH: the fclass mask and binary64's fields), 3 (WORD:
   tag JNum), 2 ^ 64 2 ^ 47 2 ^ 32 2 ^ 30 2 ^ 23 4096 (LENGTH: address and length ranges). No ADDRESS.
   THE KIT-TEXT ADAPTATION (lane A'End, worker a Theorem Labs lane, base 6b723d760c66: the kit's
   post-implication reader text by path from a working branch 3ac20a5c9e30, PRH_FnParse.v 94232293d483,
   PRH_Base.v ee2f5cd7ed35). STATEMENTS MOVED, each forced by a text: vne_sep and vrd_num_end_stmt take the ledger
   FIELDS `most own` after `ran` (PRH_Base.prh_ledger); vrd_num_end_stmt drops the six rp_* parameters (the boundary
   vrd_num299_a and the result vrd_pv_post state the room position as the post-implication transfer from S0). No
   lemma renamed. THE PROOF: the ledger move is rd_ledger_move's #102 form (most, the all-granted trace
   prhPv_gtrace, the refusal peak; VrdLedgerEv.vle_alloc), the granted run is the instance's run on the success arm
   (HJV0 / HGT: ok = [] and ok = [true] give the same answer and trace), and the boundary's transfer, live-set and hull
   use conjuncts from S0 to the post-malloc state are carried to the join unchanged (rows 299..328 move no allocator
   state); the outcome clause follows from them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a YK0j YN3v YG0s YP07 YP0a YG0p YP0d YP0c YC80 YImgTop YC1fP YC80x YC1fPx YC80xf
YGcallx YCbqGcall YGcallSx YGcallMx FCiface YStrtodRowX YFclsStep YK0u YN01 YSRrMemnorm YC80xf_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip PresetRoomPos PjReqBound.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require SoftFloat FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog VrdPro VrdNum
VrdNumTail VrdRefJoinP VrdLedgerStep VrdLedgerEv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import strtod_c strtod_row S1Ledger.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure facts the walk's branches read ---- *)

(* the byte at end = res + cc of txt ++ [0] is zero iff strtod consumed the whole token (transcribed from
   a working branch da73e1570f8 lib/A/Prog/S8aNumD.v:206-218 evD_end_byte) *)
Lemma vne_end_byte : forall (txt : list Z) (cn : Z),
  Forall (fun z => numch z = true) txt -> 0 <= cn <= Z.of_nat (length txt) ->
  (nth (Z.to_nat cn) (txt ++ [0]) 0 =? 0) = (cn =? Z.of_nat (length txt)).
Proof.
  intros txt cn Hall Hcn.
  destruct (Z.eqb_spec cn (Z.of_nat (length txt))) as [E|NE].
  - rewrite E, Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - rewrite app_nth1 by lia.
    assert (Hin : In (nth (Z.to_nat cn) txt 0) txt) by (apply nth_In; lia).
    rewrite Forall_forall in Hall. specialize (Hall _ Hin). cbv beta in Hall.
    destruct (Z.eqb_spec (nth (Z.to_nat cn) txt 0) 0) as [E0|NE0]; [|reflexivity].
    rewrite E0 in Hall. vm_compute in Hall. discriminate Hall.
Qed.

(* the fclass.d mask 0x381 (bit 0 -inf, 7 +inf, 8 sNaN, 9 qNaN) is zero iff the bits are finite; the register holds
   bits mod 2 ^ 64 (transcribed from S8aNumD.v:222-243 evD_exp_mod / evD_fclass) *)
Lemma vne_exp_mod : forall bits : Z,
  Z.land (Z.shiftr (bits mod 2 ^ 64) 52) 2047 = Z.land (Z.shiftr bits 52) 2047.
Proof.
  intros bits. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases n 11) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - assert (H2047 : Z.testbit 2047 n = false).
    { apply Z.bits_above_log2; [lia|]. change (Z.log2 2047) with 10. lia. }
    rewrite H2047, !andb_false_r. reflexivity.
Qed.

Lemma vne_fclass_mod : forall bits : Z,
  (Z.land (fp_class fmt_double (bits mod 2 ^ 64)) 897 =? 0) = finite bits.
Proof.
  intros bits. unfold fp_class, finite. cbv zeta.
  unfold fp_exp_field.
  change (fp_mw fmt_double) with 52. change (Z.ones (fp_ew fmt_double)) with 2047.
  rewrite vne_exp_mod.
  destruct (Z.land (Z.shiftr bits 52) 2047 =? 2047);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* rows 313..314's value: snez of the class masked by 0x381 *)
Lemma vne_U_cls : forall E K, U E (SOff 10 0) = K -> 0 <= K < 1024 ->
  U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_AND (SOff 10 0) (SLit 897))) = (if Z.land K 897 =? 0 then 0 else 1).
Proof.
  intros E K HK HKr. rewrite !U_SAlu, !U_SLit, HK. cbn [zalu_raw].
  assert (HL : 0 <= Z.land K 897 < 2 ^ 10) by (apply (fp_Z_land_range_l 10); lia).
  rewrite (YP0m.zcanon_small 0) by lia. rewrite (YP0m.zcanon_small 897) by lia.
  rewrite (YP0m.zcanon_small (Z.land K 897)) by lia.
  destruct (Z.eqb_spec (Z.land K 897) 0) as [E0|E0].
  - rewrite E0. reflexivity.
  - replace (0 <? Z.land K 897) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* ---- the token (pure): vrd_num_tok's answer is a prefix of the rest, all numch bytes, never empty ---- *)
Lemma vne_span : forall (Pb : Z -> bool) z a r, span Pb z = (a, r) -> z = a ++ r /\ Forall (fun c => Pb c = true) a.
Proof.
  intros Pb. induction z as [|b z IH]; intros a r H; cbn [span] in H.
  - injection H as <- <-. split; [reflexivity | constructor].
  - destruct (Pb b) eqn:Pbb.
    + destruct (span Pb z) as [a1 r1] eqn:E. injection H as <- <-.
      destruct (IH a1 r1 eq_refl) as [-> HF]. split; [reflexivity | constructor; assumption].
    + injection H as <- <-. split; [reflexivity | constructor].
Qed.

Lemma vne_tok_spec : forall x txt r, vrd_num_tok x = Some (txt, r) ->
  x = txt ++ r /\ Forall (fun c => numch c = true) txt /\ (1 <= length txt)%nat.
Proof.
  intros x txt r H. destruct x as [|b y]; [discriminate H|].
  unfold vrd_num_tok in H. cbn beta iota zeta in H.
  destruct (skipn (vrd_j b) (b :: y)) as [|c z] eqn:Es; [discriminate H|].
  destruct (digit c) eqn:Dc; cbn [negb] in H; [|discriminate H].
  destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end)%bool; [discriminate H|].
  destruct (span numch z) as [a r0] eqn:Ez. injection H as <- <-.
  destruct (vne_span numch z a r0 Ez) as [Hz HF].
  split; [|split].
  - transitivity (firstn (vrd_j b) (b :: y) ++ skipn (vrd_j b) (b :: y)); [symmetry; apply firstn_skipn|].
    rewrite Es, Hz, <- app_assoc. reflexivity.
  - apply Forall_app; split.
    + unfold vrd_j. destruct (Z.eqb_spec b 45) as [->|]; cbn [firstn];
        [constructor; [reflexivity | constructor] | constructor].
    + constructor; [unfold numch; rewrite Dc; reflexivity | exact HF].
  - rewrite length_app. cbn [length]. lia.
Qed.

(* the token is one numch run inside the text, so its length is at most the text's longest run (PjRoundTrip.maxrun) *)
Lemma vne_mr_suffix : forall U X c, (PjRoundTrip.mr 0 X <= PjRoundTrip.mr c (U ++ X))%nat.
Proof.
  induction U as [|b U IH]; intros X c; cbn [app PjRoundTrip.mr].
  - apply PjRoundTrip.mr_mono. lia.
  - destruct (numch b); [apply IH | specialize (IH X 0%nat); lia].
Qed.

Lemma vne_mr_run : forall txt X c, Forall (fun b => numch b = true) txt ->
  (c + length txt <= PjRoundTrip.mr c (txt ++ X))%nat.
Proof.
  induction txt as [|b t IH]; intros X c HF; cbn [app length PjRoundTrip.mr].
  - pose proof (PjRoundTrip.mr_ge X c). lia.
  - inversion HF as [|? ? Hb Ht]; subst. rewrite Hb. specialize (IH X (S c) Ht). lia.
Qed.

Lemma vne_txt_len : forall (tb : list Z) text p' txt r, rest_atR tb text p' = txt ++ r ->
  Forall (fun c => numch c = true) txt -> (length txt <= PjRoundTrip.maxrun tb)%nat.
Proof.
  intros tb text p' txt r H HF. unfold PjRoundTrip.maxrun.
  rewrite <- (firstn_skipn (Z.to_nat (p' - text)) tb). unfold rest_atR in H. rewrite H.
  pose proof (vne_mr_suffix (firstn (Z.to_nat (p' - text)) tb) (txt ++ r) 0) as H1.
  pose proof (vne_mr_run txt r 0 HF) as H2. lia.
Qed.

Lemma vne_numch_rng : forall c, numch c = true -> 0 < c < 256.
Proof.
  intros c H. unfold numch, digit in H.
  destruct (Z.leb_spec 48 c), (Z.leb_spec c 57), (Z.eqb_spec c 46), (Z.eqb_spec c 101), (Z.eqb_spec c 69),
    (Z.eqb_spec c 43), (Z.eqb_spec c 45); cbn in H; try discriminate H; lia.
Qed.

(* strtod's bits are a word (RESTATEMENT of the released plain lib/Prog/PvNum.v:202-223 pvn_r64 / pvn_to_d_range,
   which loads the plain kit; the land case uses YK0o.fp_Z_land_range_l) *)
Local Ltac vne_r64 :=
  lazymatch goal with
  | |- 0 <= Z.lor _ _ < 2 ^ 64 => apply Z_lor_range; vne_r64
  | |- 0 <= Z.lxor _ _ < 2 ^ 64 => apply Z_lxor_range; vne_r64
  | |- 0 <= Z.shiftr _ _ < 2 ^ 64 => apply Z_shiftr_range; [vne_r64 | first [lia | apply Z.land_nonneg; right; lia]]
  | |- 0 <= Z.land _ _ < 2 ^ 64 => apply (fp_Z_land_range_l 64); [lia | vne_r64]
  | |- 0 <= SoftFloat.wrap64 _ < 2 ^ 64 => apply SoftFloat.wrap64_range
  | |- 0 <= (if ?c then _ else _) < 2 ^ 64 => destruct c; vne_r64
  | |- _ => lia
  end.

Lemma vne_to_d_range : forall a, 0 <= SoftFloat.f128_to_d a < 2 ^ 64.
Proof.
  intros a. unfold SoftFloat.f128_to_d. cbv zeta.
  repeat match goal with |- context [if ?c then pair _ _ else _] => destruct c end;
  cbv iota beta;
  cbv beta delta [SoftFloat.shl64 SoftFloat.add64 SoftFloat.sub64 SoftFloat.lo64 SoftFloat.hi64 SoftFloat.trunc_round
    SoftFloat.nez64 SoftFloat.eqz64 SoftFloat.b2z SoftFloat.sra63 SoftFloat.zext32 SoftFloat.sext32 SoftFloat.DQUIET].
  all: vne_r64.
Qed.

Lemma vne_bits_range : forall txt bits cc, vrd_sm txt = Some (bits, cc) -> 0 <= bits < 2 ^ 64.
Proof.
  intros txt bits cc H. unfold vrd_sm, prh_jr_strtod in H.
  destruct (FloatScan.scan_strtod (txt ++ [0])) as [[b c]|] eqn:E; cbn [fst snd] in H; injection H as <- _; [|lia].
  unfold FloatScan.scan_strtod in E.
  destruct (FloatScan.floatscan _ _ _ _) as [[f y]|]; [|discriminate E].
  injection E as <- _. apply vne_to_d_range.
Qed.

(* the two pairwise-disjointness reads the separation argument needs *)
Lemma vne_pw_app : forall (A B0 : list (Z * Z)) x y, pairwise zdisjoint (A ++ B0) -> In x A -> In y B0 ->
  zdisjoint x y.
Proof.
  intros A B0 x y H Hx Hy. apply in_split in Hx as (l1 & l2 & ->). apply in_split in Hy as (l3 & l4 & ->).
  apply (pairwise_In2 zdisjoint _ x y l1 (l2 ++ l3) l4 H). rewrite <- !app_assoc. reflexivity.
Qed.

Lemma vne_pw_map2 : forall (f : Z * Z -> Z * Z) (A R : list (Z * Z)) x y,
  pairwise zdisjoint (map f A ++ R) -> In x A -> In y A -> x <> y -> zdisjoint (f x) (f y).
Proof.
  intros f A R x y H Hx Hy Hne. apply pairwise_app_l in H as [H _].
  apply (pairwise_zdisjoint_split (map f A) (f x) (f y) H).
  destruct (in_split_2 x y A Hx Hy Hne) as (l1 & l2 & l3 & [E|E]); rewrite E;
    exists (map f l1), (map f l2), (map f l3); [left | right];
    repeat (first [rewrite map_app | progress cbn [map]]); reflexivity.
Qed.

(* a refused node: its header with only the str word set, the one block it owns, freeable at any depth *)
Lemma vne_fd_str : forall (sg : list Segment) m (lblk : Z -> Z -> Prop) (dd : nat) v ty num str k,
  pj_hdrR sg m v ty num str 0 0 0 0 -> lblk str k -> pj_apartR [(str, k)] v -> pj_fdR sg m lblk dd v [(str, k)].
Proof.
  intros sg m lblk dd v ty num str k HH Hl Ha.
  assert (HN : NoDup [(str, k)]) by (repeat constructor; intros Hc; inversion Hc).
  destruct dd as [|dd]; cbn [pj_fdR]; unfold pj_fshapeR; (split; [exact HN|]); (split; [exact Ha|]);
    exists ty, num, str, 0, 0, 0, 0, false, [(str, k)], [], [], [];
    (split; [exact HH|]); (split; [right; exists k; split; [exact Hl | reflexivity]|]);
    (split; [left; repeat split|]); (split; [left; repeat split|]);
    (split; [cbn [app]; apply Permutation_refl|]).
  - repeat split.
  - reflexivity.
Qed.

(* ======================================================================================================== *)
(* PART A: THE MACHINE, rows 299..326, at the run's float state (the Section's fx is strtod's fx2 here)      *)
(* ======================================================================================================== *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B prh_pst ARx).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
(* the memory invariant the segment keeps (its instance: the memnorm keep from the entry memory, YSRrMemnorm.v's
   srr_inv_laws_imp over srr_inv_laws_memnorm_k) *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.

(* ---- one store of a byte list through the restricted view (transcribed from a working branch
   da73e1570f8 lib/A/Prog/S8aNumD.v:259-333, evD_store_ok .. evD_aview_out; that file is not in this build set) ---- *)
Lemma vne_store_ok : forall (m : word -> option byte) (n : nat) (a : Z),
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (a + i)) <> None) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
  intros m n. induction n as [|n IH]; intros a Hp Ha Hn; [reflexivity|].
  cbn [store_ok]. unfold wview.
  destruct (m (Z_to_bv 64 a)) eqn:E.
  - rewrite Z_to_bv64_add1. apply IH; [| lia | lia].
    intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hp. lia.
  - exfalso. apply (Hp 0); [lia|]. rewrite Z.add_0_r. exact E.
Qed.

Lemma vne_wb_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (x : word),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  (bv_unsigned x < A \/ A + Z.of_nat (length bs) <= bv_unsigned x) ->
  mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) x = mrestrict H mem x.
Proof.
  intros H mem A bs x HA HAn Hx. unfold munrestrict, mrestrict.
  destruct (H x) eqn:Hh; [reflexivity|].
  rewrite wbytes_outside; [cbv beta; rewrite Hh; reflexivity | rewrite YK00.u64_lit by lia; lia |].
  rewrite YK00.u64_lit by lia. exact Hx.
Qed.

Lemma vne_wb_hid : forall (H : word -> bool) (mem m' : word -> option byte) (x : word),
  H x = true -> munrestrict H mem m' x = mem x.
Proof. intros H mem m' x Hh. unfold munrestrict. rewrite Hh. reflexivity. Qed.

Lemma vne_wb_grow : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  mem_grows (mrestrict H mem) (mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs))).
Proof.
  intros H mem A bs HA HAn x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [Hl|Hl]; [rewrite vne_wb_out by lia; exact Hx|].
  destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (length bs))) as [Hu|Hu];
    [|rewrite vne_wb_out by lia; exact Hx].
  unfold mrestrict in *. unfold munrestrict. destruct (H x) eqn:Hh; [exact Hx|].
  rewrite wbytes_inside; [discriminate | rewrite YK00.u64_lit by lia; lia | rewrite YK00.u64_lit by lia; lia].
Qed.

Lemma vne_wb_in : forall (H : word -> bool) (mem : word -> option byte) (A v : Z) (k : nat),
  0 <= A -> A + 8 <= 2 ^ 64 -> (k < 8)%nat -> H (Z_to_bv 64 (A + Z.of_nat k)) = false ->
  mbyte segs (mrestrict H (munrestrict H mem
      (wbytes (mrestrict H mem) (Z_to_bv 64 A) (word_to_le_bytes 8 (Z_to_bv 64 v))))) (A + Z.of_nat k)
  = Some (Z_to_bv 8 (le_byte v 8 k)).
Proof.
  intros H mem A v k HA HA8 Hk Hh.
  assert (Hlen : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 v))) = 8)
    by (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; reflexivity).
  assert (E : nth_error (word_to_le_bytes 8 (Z_to_bv 64 v)) k = Some (Z_to_bv 8 (le_byte v 8 k))).
  { unfold word_to_le_bytes. rewrite nth_error_Z_to_le_bytes by lia. f_equal.
    rewrite le_byte_bv by lia. rewrite Z_to_bv_unsigned. reflexivity. }
  unfold mbyte, munrestrict, mrestrict. rewrite Hh.
  rewrite wbytes_inside; [| rewrite YK00.u64_lit by lia; lia | rewrite !YK00.u64_lit by lia; lia].
  rewrite !YK00.u64_lit by lia. replace (A + Z.of_nat k - A) with (Z.of_nat k) by lia. rewrite Nat2Z.id.
  f_equal. apply nth_error_nth. exact E.
Qed.

Lemma vne_aview_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (z : Z),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  (z < A \/ A + Z.of_nat (length bs) <= z) ->
  aview segs H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) z = aview segs H mem z.
Proof.
  intros H mem A bs z HA HAn Hz Hout. apply aview_eq_of. apply vne_wb_out; [lia | lia |].
  rewrite YK00.u64_lit by lia. exact Hout.
Qed.

(* ONE HAND STEP (YSRrMemnorm.SRr_step_inv, YA0n.SRr_step with P on both memories) at a machine state in mkst form:
   the restricted step's answer, put back under the hidden part of the memory *)
Lemma vne_hstep : forall (W : world segs) regs pc mem md regs' pc' m' (Q : world segs -> config -> Prop),
  RiscvSemantics.step segs (mkst regs pc (mrestrict (w_H W) mem) (seg_rom segs)) =
    MachineOk (mkst regs' pc' m' (seg_rom segs)) ->
  P mem ->
  (forall md', same_but_materialized md md' -> P (munrestrict (w_H W) mem m') ->
     SRr segs W (mkCfg (mkst regs' pc' (munrestrict (w_H W) mem m') (seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (mkst regs pc mem (seg_rom segs)) md) Q.
Proof.
  intros W regs pc mem md regs' pc' m' Q Hst HPm HK.
  eapply (SRr_step_inv segs (@pa_wx _ _ PI_prog_A) P PLAW W);
    [reflexivity | rewrite restrict_mkst_fx; exact Hst | exact HPm |].
  intros md' Hs HPm'. exact (HK md' Hs HPm').
Qed.

(* a step that moves only the model: the journal follows (YCbqG.ajournal_x_exec_fr with an empty write set) *)
Lemma vne_aj_model : forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc (W : world segs) mem md md' k,
  AJ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md k -> same_but_materialized md md' ->
  AJ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md' k.
Proof.
  intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem md md' k HJ Hs.
  apply (ajournal_x_exec_fr (SK := SK) segs B prh_pst ARx LAWS (@pa_segs_low _ _ PI_prog_A)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a [].
Qed.

(* bytes that read 0 are a 0 value *)
Lemma vne_val0 : forall (H : word -> bool) (m : word -> option byte) a (w : nat),
  (forall i, a <= i < a + Z.of_nat w -> aview segs H m i = Some 0) -> val_mem segs (mrestrict H m) a w 0.
Proof.
  intros H m a w HZ k Hk. pose proof (HZ (a + Z.of_nat k) ltac:(lia)) as E. unfold aview in E.
  destruct (mbyte segs (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate E].
  cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. rewrite E, Z_to_bv_unsigned.
  unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.

(* the registers the join reads (VrdNum.vrd_ref_a): s0, s2, s8, s10, gp, tp; s5 apart *)
Definition vne_kl : list (bv 5) := [3%bv; 4%bv; 8%bv; 18%bv; 24%bv; 26%bv].
Definition vne_kept (regs' regs : bvmap 5 word) : Prop := forall r, In r vne_kl -> getr regs' r = getr regs r.
Lemma vne_kept_trans : forall r3 r2 r1, vne_kept r3 r2 -> vne_kept r2 r1 -> vne_kept r3 r1.
Proof. intros r3 r2 r1 H32 H21 r Hr. rewrite (H32 r Hr). exact (H21 r Hr). Qed.
(* the registers the runs of rows 299..312 leave alone (all of them their own atom in those states), and those of
   rows 313..326 (s11 is pinned there; s5 is written at row 324) *)
Definition vne_kl2 : list (bv 5) := [3%bv; 4%bv; 8%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 26%bv; 27%bv].
Definition vne_kl3 : list (bv 5) := [3%bv; 4%bv; 8%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 24%bv; 26%bv].
Definition vne_kl4 : list (bv 5) := [3%bv; 4%bv; 8%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 26%bv].

(* ---- the tactics (VrdNumTail.v's are Local there; these take every hypothesis as a parameter) ---- *)
Local Ltac vne_rl Hin :=
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change l with l' in Hin end;
  cbn [In] in Hin.
Local Ltac vne_inw :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vne_rl Hin; repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => rewrite Hu in Hr end; lia.
Local Ltac vne_keep Ha64 :=
  first [ lazymatch goal with |- ?x = ?x => reflexivity end
        | match goal with
          | HFx : frame_of _ ?rs (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2) |- aview _ ?Hh ?m2 ?a = _ =>
              transitivity (aview segs Hh m1 a);
              [ apply (vrd_fr_aview _ rs Hh m1 m2 a HFx Ha64); vne_inw | clear HFx; vne_keep Ha64 ]
          end ].
(* a run's own presence growth (the post's mem_grows), from its start memory to its end memory *)
Local Ltac vne_grow := assumption.
Local Ltac vne_valg HS bnat off :=
  let go EE ssq :=
    let l := eval vm_compute in (ss_mem ssq) in
    lazymatch l with context [YP09.mkRegion (Some bnat) ?lo ?hi ?wlo ?whi ?cs] =>
      lazymatch cs with context [YP09.mkChunk off (CVal ?nn ?ev)] =>
        first [ eapply (vrd_val_at EE ssq _ _ (Some bnat) lo hi wlo whi cs off nn ev _ _ HS)
              | eapply (vrd_val_at_ok EE ssq _ _ (Some bnat) lo hi wlo whi cs off nn ev _ _ HS) ];
        [ change (ss_mem ssq) with l; cbn [In]; repeat (first [left; reflexivity | right])
        | cbn [In]; repeat (first [left; reflexivity | right])
        | .. ]
      end end in
  lazymatch type of HS with
  | st_ok_pi _ _ ?EE ?ssq _ => go EE ssq
  | st_ok _ ?EE ?ssq _ => go EE ssq
  end.
Local Ltac vne_regv HS r ev val Hu :=
  let Q := fresh "Q" in
  first [ pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as Q
        | pose proof (st_ok_restrict_reg segs _ _ _ _ r HS) as Q ];
  lazymatch type of Q with _ = sv_denot _ ?t => replace t with ev in Q by (vm_compute; reflexivity) end;
  rewrite (vrd_sv_eq _ ev val Hu) in Q; exact Q.
Local Ltac vne_kept_l HS HAE l :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  first [ exact (regs_kept_of_st_ok_pi _ _ _ _ _ l HS HAE ltac:(vm_compute; reflexivity) r Hr)
        | exact (regs_kept_of_st_ok segs _ _ _ _ _ l HS HAE ltac:(vm_compute; reflexivity) r Hr) ].
(* a run's write premise: every write window is the node's or the cursor's (HWN / HWQ), or there is none *)
Local Ltac vne_wr HWN HWQ :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vne_rl Hin; repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => rewrite Hu in Hr end;
  first [ exfalso; lia | apply HWN; lia | apply HWQ; lia ].
(* membership in a literal register list *)
Local Ltac vne_in := cbn [In vne_kl vne_kl2 vne_kl3 vne_kl4]; repeat (first [left; reflexivity | right]).
Local Ltac vne_sub Hr := unfold vne_kl, vne_kl2, vne_kl3, vne_kl4 in *; cbn [In] in Hr |- *; intuition.
(* the listing word at a row and its decoding *)
Local Ltac vne_fetch row instr :=
  let k := eval vm_compute in (vrd_row row) in
  let e := eval vm_compute in (plookup (@pl_tpi _ PL_prog_A) k) in
  lazymatch e with
  | Some (PW ?w) =>
    let Hf := fresh "Hf" in let Hd := fresh "Hd" in let He := fresh "He" in
    pose proof (pa_fetch_pw (PL := PL_prog_A) (PI := PI_prog_A) (vrd_row row) w ltac:(vm_compute; reflexivity)) as Hf;
    assert (Hd : decode_any (Z_to_bv 32 w) = Some (instr, 4%Z))
      by (vm_compute; repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]);
    assert (He : is_ecall (Z_to_bv 32 w) = false) by (vm_compute; reflexivity)
  end.

(* ---- the state at row 299 (A 0x863b4): the endptr cell [fr + 32, fr + 40) holding res + cc (atom 32), the node's
   num word [v + 8, v + 16) addressable (its shadow entry), no write window. The run stops at row 305 (fsd). ---- *)
Definition vne_E1 (regs : bvmap 5 word) (x : Z) : env := @Eimg _ A_prog_listing PI_prog_A (Ereg regs [w64 x]).
Definition vne_299_regions : smem := [ YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))] ].
Definition vne_299_facts : facts := mkFacts
  [ (19%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (25%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (32%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0) ] [] [].
Definition ss_vne_299 : sstate := mkSS (vrd_row 299) sr_atoms vne_299_regions None vne_299_facts.
Definition vne_SH299 : list shent := [mkSHE 19 8 16].

Lemma vne_st_299 : forall (W : world segs) regs mem (v fr x : Z),
  getr regs 19 = w64 v -> getr regs (Z_to_bv 5 25) = w64 (fr + 32) -> getr regs 23 = w64 SHADOW_OFF ->
  4096 <= v -> v mod 8 = 0 -> v + 16 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= fr + 32 -> fr + 40 <= 2 ^ 47 - 2 ^ 23 ->
  4096 <= x <= 2 ^ 47 - 2 ^ 23 ->
  val_mem segs (rdW W mem) (fr + 32) 8 x ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (v + 8) 8 -> amem_range (v + 8) 8 ->
  st_ok_pi segs VAL (vne_E1 regs x) ss_vne_299
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 299)) mem (seg_rom segs))) /\
  sh_ok segs vrd_Bx vne_SH299 (vne_E1 regs x) (rdW W mem).
Proof.
intros W regs mem v fr x R19 R25 R23 Hv0 Hv8 Hv1 Hf0 Hf1 Hx VX RAv Amv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
set (E := vne_E1 regs x).
assert (EL : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm Hr; subst E; unfold vne_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ m r Hr)).
assert (E32 : ew E 32 = w64 x)
  by (subst E; unfold vne_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U19 : bv_unsigned (ew E 19) = v)
  by (rewrite (EL 19%nat 19%bv) by (lia || reflexivity); rewrite R19; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite (EL 23%nat 23%bv) by (lia || reflexivity); rewrite R23; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew E 25) = fr + 32)
  by (rewrite (EL 25%nat (Z_to_bv 5 25)) by (lia || reflexivity); rewrite R25; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = x) by (rewrite E32; apply unsigned_lit_small; lia).
assert (UO23 : U E (SOff 23 0) = SHADOW_OFF)
  by (rewrite U_SOff, U23, Z.add_0_r; apply YP0m.zcanon_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold vne_299_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor.
    apply (chunk_ok_val segs _ _ (fr + 32) 0 8 (SOff 32 0) x);
      [apply vrd_sv_eq; rewrite U_SOff, U32, Z.add_0_r; apply YP0m.zcanon_small; lia | cbn; lia | lia
      | rewrite Z.add_0_r; exact VX].
  + apply pairwise_disjoint_of_extents. unfold vne_299_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. tauto.
  + split; [|split; [exact I | exact I]].
    cbn [vne_299_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U23, U25, U32. change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
    repeat split; try lia; try exact I.
- unfold sh_ok, vne_SH299. repeat (apply Forall_cons); try apply Forall_nil.
  apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 19 (v + 8) 8 v 8 16 RAv).
  + unfold vrd_Bx. exact UO23.
  + rewrite YP0e.U_SOff, U19, Z.add_0_r. apply YP0m.zcanon_small. lia.
  + lia.
  + lia.
  + intros y Hy. cbn [Z.min Z.max] in Hy. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amv. lia.
Qed.

(* ---- the state at row 306 (A 0x863d0), after the fsd: a0 = res + cc, its byte b (atom 32) readable and
   addressable. The run stops at the branch of row 311. ---- *)
Definition vne_306_regions : smem := [ YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition vne_306_facts : facts := mkFacts
  [ (10%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition ss_vne_306 : sstate := mkSS (vrd_row 306) sr_atoms vne_306_regions None vne_306_facts.
Definition vne_SH306 : list shent := [mkSHE 10 0 1].

Lemma vne_st_306 : forall (W : world segs) regs mem (x b : Z),
  getr regs 10 = w64 x -> getr regs 23 = w64 SHADOW_OFF ->
  4096 <= x -> x + 1 <= 2 ^ 47 - 2 ^ 23 -> 0 <= b < 256 ->
  val_mem segs (rdW W mem) x 1 b ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x 1 -> amem_range x 1 ->
  st_ok_pi segs VAL (vne_E1 regs b) ss_vne_306
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 306)) mem (seg_rom segs))) /\
  sh_ok segs vrd_Bx vne_SH306 (vne_E1 regs b) (rdW W mem).
Proof.
intros W regs mem x b R10 R23 Hx0 Hx1 Hb VB RAx Amx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
set (E := vne_E1 regs b).
assert (EL : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm Hr; subst E; unfold vne_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ m r Hr)).
assert (E32 : ew E 32 = w64 b)
  by (subst E; unfold vne_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U10 : bv_unsigned (ew E 10) = x)
  by (rewrite (EL 10%nat 10%bv) by (lia || reflexivity); rewrite R10; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite (EL 23%nat 23%bv) by (lia || reflexivity); rewrite R23; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = b) by (rewrite E32; apply unsigned_lit_small; lia).
assert (UO23 : U E (SOff 23 0) = SHADOW_OFF)
  by (rewrite U_SOff, U23, Z.add_0_r; apply YP0m.zcanon_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold vne_306_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor.
    apply (chunk_ok_val segs _ _ x 0 1 (SOff 32 0) b);
      [apply vrd_sv_eq; rewrite U_SOff, U32, Z.add_0_r; apply YP0m.zcanon_small; lia | cbn; lia | lia
      | rewrite Z.add_0_r; exact VB].
  + apply pairwise_disjoint_of_extents. unfold vne_306_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. tauto.
  + split; [|split; [exact I | exact I]].
    cbn [vne_306_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U23, U32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; try lia; try exact I.
- unfold sh_ok, vne_SH306. repeat (apply Forall_cons); try apply Forall_nil.
  apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 10 x 1 x 0 1 RAx).
  + unfold vrd_Bx. exact UO23.
  + rewrite YP0e.U_SOff, U10, Z.add_0_r. apply YP0m.zcanon_small. lia.
  + lia.
  + lia.
  + intros y Hy. cbn [Z.min Z.max] in Hy. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amx. lia.
Qed.

(* ---- the state at row 313 (A 0x863ec), after the fclass.d: a0 = the class (atom 10, below 1024), no region and no
   write window. The run stops at the branch of row 315. ---- *)
Definition vne_313_facts : facts := mkFacts [ (10%nat, mkAF 0 1023 0) ] [] [].
Definition ss_vne_313 : sstate := mkSS (vrd_row 313) sr_atoms [] None vne_313_facts.

Lemma vne_st_313 : forall (W : world segs) regs mem (K : Z),
  getr regs 10 = w64 K -> 0 <= K <= 1023 ->
  st_ok_pi segs VAL (vrd_E regs) ss_vne_313
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 313)) mem (seg_rom segs))) /\
  sh_ok segs vrd_Bx [] (vrd_E regs) (rdW W mem).
Proof.
intros W regs mem K R10 HK.
assert (U10 : bv_unsigned (ew (vrd_E regs) 10) = K)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); rewrite R10; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. tauto.
  + split; [|split; [exact I | exact I]].
    cbn [vne_313_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; try lia; try exact I.
- apply Forall_nil.
Qed.

(* ---- the state at row 316 (A 0x863f8), the class test passed: the node's tag word [v, v + 4) and the cursor's p
   word [q, q + 8) writable and addressable, s11 pinned to the shadow address of q. The run reaches row 326. ---- *)
Definition vne_316_sr : list sv := sr_set sr_atoms 27%bv vrd_shq.
Definition vne_316_regions : smem :=
  [ YP09.mkRegion (Some 19%nat) 0 4 0 4 []; YP09.mkRegion (Some 20%nat) 0 8 0 8 [] ].
Definition vne_316_facts : facts := mkFacts
  [ (19%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 3); (20%nat, mkAF 4096 (2 ^ 47 - 8) 3);
    (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition ss_vne_316 : sstate := mkSS (vrd_row 316) vne_316_sr vne_316_regions None vne_316_facts.
Definition vne_SH316 : list shent := [mkSHE 19 0 4; mkSHE 20 0 8].

Lemma vne_st_316 : forall (W : world segs) regs mem (v q : Z),
  getr regs 19 = w64 v -> getr regs 20 = w64 q ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 (SHADOW_OFF + q / 8) ->
  4096 <= v -> v mod 8 = 0 -> v + 4 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= q -> q mod 8 = 0 ->
  q + 8 <= 2 ^ 47 ->
  (v + 4 <= q \/ q + 8 <= v) ->
  (forall o, 0 <= o < 4 -> writable_at segs (rdW W mem) (v + o)) ->
  (forall o, 0 <= o < 8 -> writable_at segs (rdW W mem) (q + o)) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 4 -> amem_range v 4 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 8 -> amem_range q 8 ->
  st_ok_pi segs VAL (vrd_E regs) ss_vne_316
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 316)) mem (seg_rom segs))) /\
  sh_ok segs vrd_Bx vne_SH316 (vrd_E regs) (rdW W mem).
Proof.
intros W regs mem v q R19 R20 R23 R27 Hv0 Hv8 Hv1 Hq0 Hq8 Hq1 Dvq Wv Wq RAv Amv RAq Amq.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
set (E := vrd_E regs).
assert (EL : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm Hr; subst E; unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ m r Hr)).
assert (U19 : bv_unsigned (ew E 19) = v)
  by (rewrite (EL 19%nat 19%bv) by (lia || reflexivity); rewrite R19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = q)
  by (rewrite (EL 20%nat 20%bv) by (lia || reflexivity); rewrite R20; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite (EL 23%nat 23%bv) by (lia || reflexivity); rewrite R23; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (UO20 : U E (SOff 20 0) = q) by (rewrite U_SOff, U20, Z.add_0_r; apply YP0m.zcanon_small; lia).
assert (UO23 : U E (SOff 23 0) = SHADOW_OFF)
  by (rewrite U_SOff, U23, Z.add_0_r; apply YP0m.zcanon_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold vne_316_sr. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate |].
    rewrite R27. symmetry. apply vrd_sv_eq. apply (vrd_U_shx _ 20 0); [exact UO20 | exact UO23 | lia].
  + vm_compute. reflexivity.
  + unfold vne_316_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Wv o Ho) | constructor].
    * rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Wq o Ho) | constructor].
  + apply pairwise_disjoint_of_extents. unfold vne_316_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
    rewrite U19, U20. unfold zdisj. cbn [fst snd]. repeat split; first [lia | left; lia | right; lia].
  + split; [|split; [exact I | exact I]].
    cbn [vne_316_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U20, U23. change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
    repeat split; try lia; try exact I.
- unfold sh_ok, vne_SH316. repeat (apply Forall_cons); try apply Forall_nil.
  + apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 19 v 4 v 0 4 RAv).
    * unfold vrd_Bx. exact UO23.
    * rewrite YP0e.U_SOff, U19, Z.add_0_r. apply YP0m.zcanon_small. lia.
    * lia.
    * lia.
    * intros y Hy. cbn [Z.min Z.max] in Hy. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amv. lia.
  + apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 20 q 8 q 0 8 RAq).
    * unfold vrd_Bx. exact UO23.
    * exact UO20.
    * lia.
    * lia.
    * intros y Hy. cbn [Z.min Z.max] in Hy. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amq. lia.
Qed.

(* ---- THE MACHINE SEGMENT, rows 299..326 (A 0x863b4..0x86420), at the run's float state: three symbolic runs
   (measured: the first stops at row 305, the second at the branch of row 311 and, falling through, at row 312, the
   third at the branch of row 315 and runs on to row 326 either way), the two hand steps, and the two continuations at
   row 326: refused (rows 311 / 315 taken, s5 still -1, only the num word written) and accepted (tag 3 at v, q->p = s6,
   s5 = 0). ---- *)
Lemma vne_seg_299_P : forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (fr res cc n s6 bits : Z) (txt : list Z) (Q : world segs -> config -> Prop),
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  P mem ->
  getr regs 19 = w64 v -> getr regs 20 = w64 q -> getr regs 22 = w64 s6 -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs (Z_to_bv 5 25) = w64 (fr + 32) -> getr regs 27 = w64 (SHADOW_OFF + q / 8) ->
  LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 10) = Z_to_bv 64 bits ->
  4096 <= v -> v mod 8 = 0 -> v + 24 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= q -> q mod 8 = 0 -> q + 8 <= 2 ^ 47 ->
  0 <= s6 < 2 ^ 64 -> 4096 <= fr + 32 -> fr + 40 <= 2 ^ 47 - 2 ^ 23 ->
  Z.of_nat (length txt) = n -> 0 <= cc <= n -> 4096 <= res -> res + n + 1 <= 2 ^ 47 - 2 ^ 23 ->
  Forall (fun c => numch c = true) txt ->
  (v + 16 <= q \/ q + 8 <= v) -> (res + n + 1 <= v \/ v + 16 <= res) ->
  val_mem segs (rdW W mem) (fr + 32) 8 (res + cc) -> garr8 segs (rdW W mem) res (txt ++ [0]) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 24 -> amem_range v 24 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 8 -> amem_range q 8 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF res (n + 1) -> amem_range res (n + 1) ->
  (forall a, v <= a < v + 16 ->
     awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly S) ly
       [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly a) ->
  (forall a, q <= a < q + 8 ->
     awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly S) ly
       [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly a) ->
  (* row 326, refused at row 311 (the token not consumed whole) or at row 315 (not finite) *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k -> P mem' ->
     vne_kept regs' regs -> getr regs' 21 = getr regs 21 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 8 <= a < v + 16) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     val_mem segs (rdW W mem') (v + 8) 8 bits ->
     ((cc =? n) && finite bits)%bool = false ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  (* row 326, accepted *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k -> P mem' ->
     vne_kept regs' regs -> getr regs' 21 = w64 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> ~ (v + 8 <= a < v + 16) -> ~ (q <= a < q + 8) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     val_mem segs (rdW W mem') v 4 3 -> val_mem segs (rdW W mem') (v + 8) 8 bits ->
     val_mem segs (rdW W mem') q 8 s6 ->
     cc = n -> finite bits = true ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 299) regs mem md) Q.
Proof.
intros d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md fr res cc n s6 bits txt Q
  HJ HPM R19 R20 R22 R23 R25 R27 FA0 Hv0 Hv8 Hv1 Hq0 Hq8 Hq1 Hs6 Hf0 Hf1 Hlen Hcc Hr0 Hr1 HNUM Dvq Drv
  VE GT RAv Amv RAq Amq RAr Amr HWN HWQ HREF HACC.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
(* the two written windows are present at the start *)
assert (HFRP : forall a, wr_fp_frame (rd_fp q v) S0 ly a -> apresent (w_H W) mem a).
{ intros a (_ & cid & pos' & Hin & Hr).
  assert (Hin' : In (cid, pos') (frames S)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (alx_frames segs B ARx LAWS ly S Hp W mem md cid pos' HAR Hin') as (_ & _ & Hb & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (proj1 (Hb a Hr)). }
assert (PV : forall a, v <= a < v + 16 -> apresent (w_H W) mem a).
{ intros a Ha. destruct (HWN a Ha) as [Hw | Hw].
  - exact (proj1 (awr_byte_present_x (SK := SK) segs B prh_pst ARx LAWS
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hw)).
  - exact (HFRP _ Hw). }
assert (PQ : forall a, q <= a < q + 8 -> apresent (w_H W) mem a).
{ intros a Ha. destruct (HWQ a Ha) as [Hw | Hw].
  - exact (proj1 (awr_byte_present_x (SK := SK) segs B prh_pst ARx LAWS
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hw)).
  - exact (HFRP _ Hw). }
assert (FA0' : LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fx) 10%bv = Z_to_bv 64 bits)
  by (rewrite <- FA0; f_equal; apply bv_eq; reflexivity).
assert (KSH : forall s, SHADOW_OFF <= s < kHighShadowEnd -> ~ (v <= s < v + 24) /\ ~ (q <= s < q + 8)).
{ intros s Hs. unfold kHighShadowEnd in Hs.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amv, Amq. split; lia. }
pose (RUN := paj_run_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
(* ======== rows 299..304 ======== *)
assert (RAv8 : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (v + 8) 8)
  by (apply (vrd_ra_sub _ _ v 24); [exact RAv | lia | lia]).
assert (Amv8 : amem_range (v + 8) 8) by (apply (vrd_amem_sub v 24); [exact Amv | lia | lia | lia]).
destruct (vne_st_299 W regs mem v fr (res + cc) R19 R25 R23 Hv0 Hv8 ltac:(lia) Hf0 Hf1 ltac:(lia) VE RAv8 Amv8)
  as [HS SHOK].
set (E := vne_E1 regs (res + cc)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold vne_E1; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 (res + cc)]) E)
  by (subst E; split; [intros nn Hnn; unfold vne_E1; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm Hr; subst E; unfold vne_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ m r Hr)).
assert (E32 : ew E 32 = w64 (res + cc))
  by (subst E; unfold vne_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U19 : bv_unsigned (ew E 19) = v)
  by (rewrite (EL 19%nat 19%bv) by (lia || reflexivity); rewrite R19; apply unsigned_lit_small; lia).
assert (UO198 : U E (SOff 19 8) = v + 8) by (rewrite U_SOff, U19; apply YP0m.zcanon_small; lia).
assert (UO32 : U E (SOff 32 0) = res + cc)
  by (rewrite U_SOff, E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; apply YP0m.zcanon_small; lia).
unfold cfg_at.
paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
{ vne_wr HWN HWQ. }
(* stopped at row 305, the fsd *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha64; vne_keep Ha64).
assert (MG1 : mem_grows (rdW W mem) (rdW W (ms_mem ms))) by vne_grow.
assert (Q10 : getr (ms_regs ms) 10%bv = w64 (res + cc)) by (vne_regv HS (10%bv : bv 5) (SOff 32 0) (res + cc) UO32).
assert (Q11 : getr (ms_regs ms) 11%bv = w64 (v + 8)) by (vne_regv HS (11%bv : bv 5) (SOff 19 8) (v + 8) UO198).
assert (KK1 : forall r, In r vne_kl2 -> getr (ms_regs ms) r = getr regs r) by (vne_kept_l HS HAE vne_kl2).
rewrite ?wvb_collapse in HJ.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (md1 := mdq) in * end. clearbody md1.
pmkst HS.
change (BASE + 19948) with (BASE + vrd_row 305).
clear HS SHOK HEI HAE EL E32 UO198 UO32.
(* ======== row 305: fsd fa0, 0(a1), ONE HAND STEP ======== *)
vne_fetch 305%nat (FStore FMT_D 11%bv 10%bv 0%bv).
assert (Ha : YK11.v_addi (getr (ms_regs ms) 11%bv) (bv_signed (0%bv : bv 12)) = Z_to_bv 64 (v + 8)).
{ rewrite Q11. unfold w64. rewrite YCbn.v_addi_lit. f_equal.
  replace (bv_signed (0%bv : bv 12)) with 0 by (vm_compute; reflexivity). lia. }
assert (Hok : store_ok segs (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 (v + 8)) 8 = true).
{ apply vne_store_ok; [| lia | lia]. intros i Hi.
  destruct (vrd_pres_of_mg _ _ _ (v + 8 + i) MG1 (PV (v + 8 + i) ltac:(lia))) as [Hh [bb Hb]].
  unfold mrestrict. rewrite Hh, Hb. discriminate. }
set (m2' := wbytes (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 bits))).
eapply (vne_hstep W (ms_regs ms) _ (ms_mem ms) md1 (ms_regs ms) (Z_to_bv 64 (BASE + vrd_row 306)) m2' Q).
{ rewrite (fp_step_fsd fx segs (ms_regs ms) _ (mrestrict (w_H W) (ms_mem ms)) (seg_rom segs) _ 11%bv 10%bv 0%bv
           (Z_to_bv 64 (v + 8)) Hf He Hd Ha Hok).
  rewrite FA0', YCbn.v_addi_lit. unfold m2'. do 3 f_equal; try (unfold vrd_row; lia). }
{ exact HPM. }
clear Hf Hd He Ha Hok HPM.
intros md2 Hsm2 HPM.
set (m2 := munrestrict (w_H W) (ms_mem ms) m2') in *.
assert (Hbl8 : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 bits))) = 8)
  by (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; reflexivity).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 8 <= a < v + 16) ->
          aview segs (w_H W) m2 a = aview segs (w_H W) (ms_mem ms) a).
{ intros a Ha Hn. unfold m2, m2'. apply vne_aview_out; rewrite ?Hbl8; lia. }
assert (MG2 : mem_grows (rdW W (ms_mem ms)) (rdW W m2)) by (unfold m2, m2'; apply vne_wb_grow; rewrite ?Hbl8; lia).
assert (VB2 : val_mem segs (rdW W m2) (v + 8) 8 bits).
{ intros kk Hkk. unfold m2, m2'. apply vne_wb_in; [lia | lia | exact Hkk |].
  destruct (vrd_pres_of_mg _ _ _ (v + 8 + Z.of_nat kk) MG1 (PV (v + 8 + Z.of_nat kk) ltac:(lia))) as [Hh _].
  exact Hh. }
assert (HJ2 : AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
                ly S Hp W m2 md2 k).
{ apply (ajournal_x_exec_fr (SK := SK) segs B prh_pst ARx LAWS (@pa_segs_low _ _ PI_prog_A)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a => v + 8 <= a < v + 16) HJ).
  - intros x Hx. unfold m2, m2'. pose proof (bv_unsigned_in_range 64 x) as Hxr. unfold bv_modulus in Hxr.
    apply vne_wb_out; rewrite ?Hbl8; lia.
  - exact MG2.
  - intros x Hx. unfold m2. apply vne_wb_hid. exact Hx.
  - exact Hsm2.
  - intros a Ha. apply HWN. lia. }
clear HJ.
assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 8 <= a < v + 16) ->
          aview segs (w_H W) m2 a = aview segs (w_H W) mem a)
  by (intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha)).
assert (MG12 : mem_grows (rdW W mem) (rdW W m2)) by (apply (vrd_mg_trans _ (rdW W (ms_mem ms))); assumption).
assert (KS12 : forall s, SHADOW_OFF <= s < kHighShadowEnd -> aview segs (w_H W) m2 s = aview segs (w_H W) mem s).
{ intros s Hs. pose proof (KSH s Hs) as [Hs1 Hs2]. unfold kHighShadowEnd in Hs. apply K12; lia. }
(* ======== rows 306..311: the byte at res + cc ======== *)
set (b := nth (Z.to_nat cc) (txt ++ [0]) 0).
assert (GT2 : garr8 segs (rdW W m2) res (txt ++ [0])).
{ apply (vrd_garr8_keep (w_H W) mem m2); [|exact GT]. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  apply K12; lia. }
destruct (vrd_garr8_byte (rdW W m2) res (txt ++ [0]) (res + cc) GT2 ltac:(rewrite length_app; cbn [length]; lia))
  as [VB HbR].
replace (res + cc - res) with cc in VB, HbR by lia. fold b in VB, HbR.
assert (RAx : range_addressable (aview segs (w_H W) m2) SHADOW_OFF (res + cc) 1).
{ apply (vrd_ra_sub _ _ res (n + 1)); [| lia | lia].
  apply (vrd_ra_shkeep (w_H W) (w_H W) mem m2); [lia | lia | exact KS12 | exact RAr]. }
assert (Amx : amem_range (res + cc) 1) by (apply (vrd_amem_sub res (n + 1)); [exact Amr | lia | lia | lia]).
assert (R23b : getr (ms_regs ms) 23%bv = w64 SHADOW_OFF) by (rewrite (KK1 23%bv) by vne_in; exact R23).
destruct (vne_st_306 W (ms_regs ms) m2 (res + cc) b Q10 R23b ltac:(lia) ltac:(lia) HbR VB RAx Amx) as [HS2 SHOK2].
set (E2 := vne_E1 (ms_regs ms) b) in *.
assert (HEI : img_env VAL A_LIM E2) by (subst E2; unfold vne_E1; apply Eimg_env).
assert (EL2 : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew E2 m = getr (ms_regs ms) r)
  by (intros m r Hm Hr; subst E2; unfold vne_E1; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_nat (ms_regs ms) _ m r Hr)).
assert (E32b : ew E2 32 = w64 b)
  by (subst E2; unfold vne_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms) _ 0)).
assert (UO32b : U E2 (SOff 32 0) = b)
  by (rewrite U_SOff, E32b, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; apply YP0m.zcanon_small; lia).
paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM vrd_Bspan.
{ vne_wr HWN HWQ. }
(* stopped at the branch of row 311 *)
lazymatch type of HS2 with st_ok_pi _ _ ?E' _ _ => set (E2' := E') in * end.
assert (HAE2 : env_agree 32 (Ereg (ms_regs ms) [w64 b]) E2').
{ subst E2'. split; [|reflexivity]. intros nn Hnn. rewrite !ew_ewset_other by lia.
  subst E2. unfold vne_E1. apply Eimg_low. unfold A_TEXT. lia. }
assert (UO32b' : U E2' (SOff 32 0) = b) by (subst E2'; rewrite !vrd_U_ewset by lia; exact UO32b).
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) m2 a)
  by (intros a Ha64; vne_keep Ha64).
assert (MG3 : mem_grows (rdW W m2) (rdW W (ms_mem ms0))) by vne_grow.
psrr_branch_tok RUN BR HS2 SHOK2 vrd_Bspan.
- (* row 311 taken: the byte is not the NUL, the token was not consumed whole *)
  rename Hc into H311.
  rewrite YI04.branch_ne_U, UO32b', U_SLit, (YP0m.zcanon_small 0) in H311 by lia.
  assert (Hcc' : (cc =? n) = false).
  { rewrite <- Hlen, <- (vne_end_byte txt cc HNUM ltac:(lia)). fold b.
    destruct (Z.eqb_spec b 0); [subst; discriminate H311 | reflexivity]. }
  paj_run_to_tok_x_inv RUNTO HS2 HJ2 SHOK2 HPM vrd_Bspan (vrd_row 326).
  { vne_wr HWN HWQ. }
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) (ms_mem ms0) a)
    by (intros a Ha64; vne_keep Ha64).
  assert (MG4 : mem_grows (rdW W (ms_mem ms0)) (rdW W (ms_mem ms1))) by vne_grow.
  assert (KK4 : forall r, In r vne_kl2 -> getr (ms_regs ms1) r = getr (ms_regs ms) r) by (vne_kept_l HS2 HAE2 vne_kl2).
  rewrite ?wvb_collapse in HJ2.
  pmkst HS2.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq ?pcq ?mq _) ?dq) _ =>
    replace (mkCfg (mkst rq pcq mq (seg_rom segs)) dq)
      with (cfg_at segs (BASE + vrd_row 326) rq mq dq)
      by (unfold cfg_at, w64; repeat f_equal; vm_compute; reflexivity) end.
  apply (HREF _ _ _ HJ2 HPM).
  + intros r Hr. assert (Hr2 : In r vne_kl2) by (vne_sub Hr). rewrite (KK4 r Hr2). exact (KK1 r Hr2).
  + rewrite (KK4 21%bv) by vne_in. exact (KK1 21%bv ltac:(vne_in)).
  + intros a Ha Hn. rewrite (K4 a Ha), (K3 a Ha). exact (K12 a Ha Hn).
  + apply (vrd_mg_trans _ (rdW W (ms_mem ms0))); [apply (vrd_mg_trans _ (rdW W m2)); assumption | exact MG4].
  + eapply val_mem_kept; [|exact VB2]. intros kk Hk. cbn in Hk. rewrite K4 by lia. apply K3. lia.
  + rewrite Hcc'. reflexivity.
- (* row 311 not taken: the NUL, strtod consumed the whole token *)
  rename Hc into H311.
  rewrite YI04.branch_ne_U, UO32b', U_SLit, (YP0m.zcanon_small 0) in H311 by lia.
  assert (Hccn : cc = n).
  { apply Z.eqb_eq. rewrite <- Hlen, <- (vne_end_byte txt cc HNUM ltac:(lia)). fold b.
    destruct (Z.eqb_spec b 0) as [Hb0|Hb0]; [reflexivity|].
    apply Z.eqb_neq in Hb0. rewrite ?Hb0 in H311. cbn in H311. discriminate H311. }
  paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM vrd_Bspan.
  { vne_wr HWN HWQ. }
  (* stopped at row 312, the fclass.d *)
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) (ms_mem ms0) a)
    by (intros a Ha64; vne_keep Ha64).
  assert (MG4 : mem_grows (rdW W (ms_mem ms0)) (rdW W (ms_mem ms1))) by vne_grow.
  assert (KK4 : forall r, In r vne_kl2 -> getr (ms_regs ms1) r = getr (ms_regs ms) r) by (vne_kept_l HS2 HAE2 vne_kl2).
  rewrite ?wvb_collapse in HJ2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (md4 := mdq) in * end. clearbody md4.
  pmkst HS2.
  change (BASE + 19976) with (BASE + vrd_row 312).
  clear HS2 SHOK2.
  set (m4 := ms_mem ms1) in *. set (r4 := ms_regs ms1) in *. clearbody m4 r4.
  assert (K14 : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 8 <= a < v + 16) ->
            aview segs (w_H W) m4 a = aview segs (w_H W) mem a)
    by (intros a Ha Hn; rewrite (K4 a Ha), (K3 a Ha); exact (K12 a Ha Hn)).
  assert (MG14 : mem_grows (rdW W mem) (rdW W m4))
    by (apply (vrd_mg_trans _ (rdW W (ms_mem ms0))); [apply (vrd_mg_trans _ (rdW W m2)); assumption | exact MG4]).
  assert (KR4 : forall r, In r vne_kl2 -> getr r4 r = getr regs r) by (intros r Hr; rewrite (KK4 r Hr); exact (KK1 r Hr)).
  (* ======== row 312: fclass.d a0, fa0, ONE HAND STEP ======== *)
  vne_fetch 312%nat (Fclass FMT_D 10%bv 10%bv).
  set (Kc := fp_class fmt_double (bits mod 2 ^ 64)).
  pose proof (vrd_fclass_range (bits mod 2 ^ 64)) as HKr. fold Kc in HKr.
  set (r5 := YK11.regupd r4 10%bv (w64 Kc)).
  eapply (vne_hstep W r4 _ m4 md4 r5 (Z_to_bv 64 (BASE + vrd_row 313)) (mrestrict (w_H W) m4) Q).
  { rewrite (fp_step_fclass_d fx segs r4 _ (mrestrict (w_H W) m4) (seg_rom segs) _ 10%bv 10%bv Hf He Hd).
    rewrite FA0', Z_to_bv_unsigned, YCbn.v_addi_lit.
    replace (BASE + vrd_row 312 + 4) with (BASE + vrd_row 313) by (unfold vrd_row; lia). reflexivity. }
  { exact HPM. }
  clear Hf Hd He HPM.
  intros md5 Hsm5 HPM. rewrite munrestrict_mrestrict in HPM |- *.
  pose proof (vne_aj_model _ _ _ _ _ _ _ _ _ _ _ _ _ W m4 md4 md5 k HJ2 Hsm5) as HJ5.
  clear HJ2.
  assert (R10c : getr r5 10%bv = w64 Kc) by (unfold r5; apply getr_same; discriminate).
  assert (R5o : forall r, r <> 10%bv -> getr r5 r = getr r4 r) by (intros r Hr; unfold r5; apply getr_other; exact Hr).
  assert (R19c : getr r5 19%bv = w64 v) by (rewrite R5o by discriminate; rewrite (KR4 19%bv) by vne_in; exact R19).
  assert (R20c : getr r5 20%bv = w64 q) by (rewrite R5o by discriminate; rewrite (KR4 20%bv) by vne_in; exact R20).
  assert (R22c : getr r5 22%bv = w64 s6) by (rewrite R5o by discriminate; rewrite (KR4 22%bv) by vne_in; exact R22).
  assert (R23c : getr r5 23%bv = w64 SHADOW_OFF)
    by (rewrite R5o by discriminate; rewrite (KR4 23%bv) by vne_in; exact R23).
  assert (R27c : getr r5 27%bv = w64 (SHADOW_OFF + q / 8))
    by (rewrite R5o by discriminate; rewrite (KR4 27%bv) by vne_in; exact R27).
  assert (Amv4 : amem_range v 4) by (apply (vrd_amem_sub v 24); [exact Amv | lia | lia | lia]).
  assert (VB4 : val_mem segs (rdW W m4) (v + 8) 8 bits)
    by (eapply val_mem_kept; [|exact VB2]; intros kk Hk; cbn in Hk; rewrite K4 by lia; apply K3; lia).
  (* ======== rows 313..315 ======== *)
  destruct (vne_st_313 W r5 m4 Kc R10c ltac:(lia)) as [HS3 SHOK3].
  assert (HEI3 : img_env VAL A_LIM (vrd_E r5)) by (unfold vrd_E; apply Eimg_env).
  assert (HAE3 : env_agree 32 (Ereg r5 []) (vrd_E r5))
    by (split; [intros nn Hnn; unfold vrd_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EL3 : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew (vrd_E r5) m = getr r5 r)
    by (intros m r Hm Hr; unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat r5 _ m r Hr)).
  assert (U10c : bv_unsigned (ew (vrd_E r5) 10) = Kc)
    by (rewrite (EL3 10%nat 10%bv) by (lia || reflexivity); rewrite R10c; apply unsigned_lit_small; lia).
  assert (UO10c : U (vrd_E r5) (SOff 10 0) = Kc) by (rewrite U_SOff, U10c, Z.add_0_r; apply YP0m.zcanon_small; lia).
  paj_run_tok_x_inv RUN HS3 HJ5 SHOK3 HPM vrd_Bspan.
  { vne_wr HWN HWQ. }
  lazymatch goal with |- SRr _ _ (mkCfg ?x _) _ => rename x into ms5 end.
  (* stopped at the branch of row 315 *)
  pose proof (vne_fclass_mod bits) as HFC. fold Kc in HFC.
  psrr_branch_tok RUN BR HS3 SHOK3 vrd_Bspan.
  + (* row 315 taken: an infinity or a NaN *)
    rename Hc into H315.
    rewrite YI04.branch_ne_U, (vne_U_cls _ Kc UO10c ltac:(lia)), U_SLit, (YP0m.zcanon_small 0) in H315 by lia.
    assert (Hfin : finite bits = false).
    { rewrite <- HFC. destruct (Z.land Kc 897 =? 0); [discriminate H315 | reflexivity]. }
    paj_run_to_tok_x_inv RUNTO HS3 HJ5 SHOK3 HPM vrd_Bspan (vrd_row 326).
    { vne_wr HWN HWQ. }
    lazymatch goal with |- SRr _ _ (mkCfg ?x _) _ => rename x into ms6 end.
    assert (K6 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) m4 a)
      by (intros a Ha64; vne_keep Ha64).
    assert (MG6 : mem_grows (rdW W m4) (rdW W (ms_mem ms6))) by (eapply vrd_mg_trans; eassumption).
    assert (KK6 : forall r, In r vne_kl2 -> getr (ms_regs ms6) r = getr r5 r) by (vne_kept_l HS3 HAE3 vne_kl2).
    rewrite ?wvb_collapse in HJ5.
    pmkst HS3.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq ?pcq ?mq _) ?dq) _ =>
      replace (mkCfg (mkst rq pcq mq (seg_rom segs)) dq)
        with (cfg_at segs (BASE + vrd_row 326) rq mq dq)
        by (unfold cfg_at, w64; repeat f_equal; vm_compute; reflexivity) end.
    apply (HREF _ _ _ HJ5 HPM).
    * intros r Hr. assert (Hr2 : In r vne_kl2) by (vne_sub Hr).
      rewrite (KK6 r Hr2), R5o by (intros ->; vne_sub Hr; discriminate). exact (KR4 r Hr2).
    * rewrite (KK6 21%bv) by vne_in. rewrite R5o by discriminate. exact (KR4 21%bv ltac:(vne_in)).
    * intros a Ha Hn. rewrite (K6 a Ha). exact (K14 a Ha Hn).
    * apply (vrd_mg_trans _ (rdW W m4)); assumption.
    * eapply val_mem_kept; [|exact VB4]. intros kk Hk. cbn in Hk. apply K6. lia.
    * rewrite Hfin, andb_false_r. reflexivity.
  + (* row 315 not taken: finite *)
    rename Hc into H315.
    rewrite YI04.branch_ne_U, (vne_U_cls _ Kc UO10c ltac:(lia)), U_SLit, (YP0m.zcanon_small 0) in H315 by lia.
    assert (Hfin : finite bits = true).
    { rewrite <- HFC. destruct (Z.land Kc 897 =? 0); [reflexivity | discriminate H315]. }
    paj_run_to_tok_x_inv RUNTO HS3 HJ5 SHOK3 HPM vrd_Bspan (vrd_row 316).
    { vne_wr HWN HWQ. }
    lazymatch goal with |- SRr _ _ (mkCfg ?x _) _ => rename x into ms6 end.
    assert (K6 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) m4 a)
      by (intros a Ha64; vne_keep Ha64).
    assert (MG6 : mem_grows (rdW W m4) (rdW W (ms_mem ms6))) by (eapply vrd_mg_trans; eassumption).
    assert (KK6 : forall r, In r vne_kl2 -> getr (ms_regs ms6) r = getr r5 r) by (vne_kept_l HS3 HAE3 vne_kl2).
    rewrite ?wvb_collapse in HJ5.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (md6 := mdq) in * end. clearbody md6.
    pmkst HS3.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq ?pcq ?mq _) ?dq) _ =>
      replace pcq with (Z_to_bv 64 (BASE + vrd_row 316)) by (f_equal; vm_compute; reflexivity) end.
    clear HS3 SHOK3.
    set (m6 := ms_mem ms6) in *. set (r6 := ms_regs ms6) in *. clearbody m6 r6.
    assert (K16 : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 8 <= a < v + 16) ->
              aview segs (w_H W) m6 a = aview segs (w_H W) mem a)
      by (intros a Ha Hn; rewrite (K6 a Ha); exact (K14 a Ha Hn)).
    assert (MG16 : mem_grows (rdW W mem) (rdW W m6)) by (apply (vrd_mg_trans _ (rdW W m4)); assumption).
    assert (R6 : forall r, In r vne_kl2 -> r <> 10%bv -> getr r6 r = getr regs r)
      by (intros r Hr Hr10; rewrite (KK6 r Hr), (R5o r Hr10); exact (KR4 r Hr)).
    assert (R19d : getr r6 19%bv = w64 v) by (rewrite R6 by (vne_in || discriminate); exact R19).
    assert (R20d : getr r6 20%bv = w64 q) by (rewrite R6 by (vne_in || discriminate); exact R20).
    assert (R22d : getr r6 22%bv = w64 s6) by (rewrite R6 by (vne_in || discriminate); exact R22).
    assert (R23d : getr r6 23%bv = w64 SHADOW_OFF) by (rewrite R6 by (vne_in || discriminate); exact R23).
    assert (R27d : getr r6 27%bv = w64 (SHADOW_OFF + q / 8)) by (rewrite R6 by (vne_in || discriminate); exact R27).
    assert (Wv : forall o, 0 <= o < 4 -> writable_at segs (rdW W m6) (v + o))
      by (intros o Ho; apply (apresent_writable segs); exact (vrd_pres_of_mg _ _ _ _ MG16 (PV (v + o) ltac:(lia)))).
    assert (Wq : forall o, 0 <= o < 8 -> writable_at segs (rdW W m6) (q + o))
      by (intros o Ho; apply (apresent_writable segs); exact (vrd_pres_of_mg _ _ _ _ MG16 (PQ (q + o) ltac:(lia)))).
    assert (KS16 : forall s, SHADOW_OFF <= s < kHighShadowEnd -> aview segs (w_H W) m6 s = aview segs (w_H W) mem s).
    { intros s Hs. pose proof (KSH s Hs) as [Hs1 Hs2]. unfold kHighShadowEnd in Hs. apply K16; lia. }
    assert (RAv6 : range_addressable (aview segs (w_H W) m6) SHADOW_OFF v 4).
    { apply (vrd_ra_sub _ _ v 24); [| lia | lia].
      apply (vrd_ra_shkeep (w_H W) (w_H W) mem m6); [lia | lia | exact KS16 | exact RAv]. }
    assert (RAq6 : range_addressable (aview segs (w_H W) m6) SHADOW_OFF q 8)
      by (apply (vrd_ra_shkeep (w_H W) (w_H W) mem m6); [lia | lia | exact KS16 | exact RAq]).
    assert (VB6 : val_mem segs (rdW W m6) (v + 8) 8 bits)
      by (eapply val_mem_kept; [|exact VB4]; intros kk Hk; cbn in Hk; apply K6; lia).
    (* ======== rows 316..326 ======== *)
    destruct (vne_st_316 W r6 m6 v q R19d R20d R23d R27d Hv0 Hv8 ltac:(lia) Hq0 Hq8 Hq1 ltac:(lia)
      Wv Wq RAv6 Amv4 RAq6 Amq) as [HS4 SHOK4].
    assert (HEIx4 : img_env VAL A_LIM (vrd_E r6)) by (unfold vrd_E; apply Eimg_env).
    assert (EL4 : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew (vrd_E r6) m = getr r6 r)
      by (intros m r Hm Hr; unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat r6 _ m r Hr)).
    assert (U19d : bv_unsigned (ew (vrd_E r6) 19) = v)
      by (rewrite (EL4 19%nat 19%bv) by (lia || reflexivity); rewrite R19d; apply unsigned_lit_small; lia).
    assert (U20d : bv_unsigned (ew (vrd_E r6) 20) = q)
      by (rewrite (EL4 20%nat 20%bv) by (lia || reflexivity); rewrite R20d; apply unsigned_lit_small; lia).
    assert (U22d : bv_unsigned (ew (vrd_E r6) 22) = s6)
      by (rewrite (EL4 22%nat 22%bv) by (lia || reflexivity); rewrite R22d; apply unsigned_lit_small; lia).
    paj_run_to_tok_x_inv RUNTO HS4 HJ5 SHOK4 HPM vrd_Bspan (vrd_row 326).
    { vne_wr HWN HWQ. }
    lazymatch goal with |- SRr _ _ (mkCfg ?x _) _ => rename x into ms7 end.
    lazymatch type of HS4 with st_ok_pi _ _ ?E' _ _ => set (E4' := E') in * end.
    assert (HAE4' : env_agree 32 (Ereg r6 []) E4').
    { subst E4'. split; [|reflexivity]. intros nn Hnn. rewrite ?ew_ewset_other by lia.
      unfold vrd_E. apply Eimg_low. unfold A_TEXT. lia. }
    assert (U19d' : bv_unsigned (ew E4' 19) = v) by (subst E4'; rewrite ?ew_ewset_other by lia; exact U19d).
    assert (U20d' : bv_unsigned (ew E4' 20) = q) by (subst E4'; rewrite ?ew_ewset_other by lia; exact U20d).
    assert (UO22d' : U E4' (SOff 22 0) = s6)
      by (subst E4'; rewrite ?vrd_U_ewset by lia; rewrite U_SOff, U22d, Z.add_0_r; apply YP0m.zcanon_small; lia).
    assert (K7 : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> ~ (q <= a < q + 8) ->
              aview segs (w_H W) (ms_mem ms7) a = aview segs (w_H W) m6 a)
      by (intros a Ha64 Hn1 Hn2; vne_keep Ha64).
    assert (MG7 : mem_grows (rdW W m6) (rdW W (ms_mem ms7))) by vne_grow.
    assert (KK7 : forall r, In r vne_kl3 -> getr (ms_regs ms7) r = getr r6 r) by (vne_kept_l HS4 HAE4' vne_kl3).
    assert (U0 : U E4' (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
    assert (Q21 : getr (ms_regs ms7) 21%bv = w64 0) by (vne_regv HS4 (21%bv : bv 5) (SLit 0) 0 U0).
    assert (VT : val_mem segs (rdW W (ms_mem ms7)) v 4 3).
    { vne_valg HS4 19%nat 0.
      - cbn [base_val]. rewrite U19d'. lia.
      - apply vrd_sv_eq. rewrite U_SLit. reflexivity.
      - cbn. lia.
      - cbn. lia. }
    assert (VQ : val_mem segs (rdW W (ms_mem ms7)) q 8 s6).
    { vne_valg HS4 20%nat 0.
      - cbn [base_val]. rewrite U20d'. lia.
      - apply vrd_sv_eq. exact UO22d'.
      - cbn. lia.
      - cbn. lia. }
    rewrite ?wvb_collapse in HJ5.
    pmkst HS4.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq ?pcq ?mq _) ?dq) _ =>
      replace (mkCfg (mkst rq pcq mq (seg_rom segs)) dq)
        with (cfg_at segs (BASE + vrd_row 326) rq mq dq)
        by (unfold cfg_at, w64; repeat f_equal; vm_compute; reflexivity) end.
    apply (HACC _ _ _ HJ5 HPM).
    * intros r Hr. assert (Hr3 : In r vne_kl3) by (vne_sub Hr). assert (Hr2 : In r vne_kl2) by (vne_sub Hr).
      rewrite (KK7 r Hr3). apply R6; [exact Hr2 | intros ->; vne_sub Hr; discriminate].
    * exact Q21.
    * intros a Ha Hn1 Hn2 Hn3. rewrite (K7 a Ha Hn1 Hn3). exact (K16 a Ha Hn2).
    * apply (vrd_mg_trans _ (rdW W m6)); assumption.
    * exact VT.
    * eapply val_mem_kept; [|exact VB6]. intros kk Hk. cbn in Hk. apply K7; lia.
    * exact VQ.
    * exact Hccn.
    * exact Hfin.
Qed.

End m.

(* ---- the machine segment's statement before the invariant (pushed Qed at preset-tree-at-2026-10-29T11-46-29Z.tsv (sha256 40aa26e3e2c9; internal record)), BYTE-IDENTICAL, as the
   P := fun _ => True corollary of vne_seg_299_P (a Theorem Labs lane's 12:18Z ruling, condition (1): the statement changed
   for P's sake only) ---- *)
Section mt. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B prh_pst ARx).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.

Lemma vne_true_laws : srr_inv_laws segs (fun _ => True).
Proof. split; intros; exact I. Qed.

Lemma vne_seg_299 : forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (fr res cc n s6 bits : Z) (txt : list Z) (Q : world segs -> config -> Prop),
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  getr regs 19 = w64 v -> getr regs 20 = w64 q -> getr regs 22 = w64 s6 -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs (Z_to_bv 5 25) = w64 (fr + 32) -> getr regs 27 = w64 (SHADOW_OFF + q / 8) ->
  LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 10) = Z_to_bv 64 bits ->
  4096 <= v -> v mod 8 = 0 -> v + 24 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= q -> q mod 8 = 0 -> q + 8 <= 2 ^ 47 ->
  0 <= s6 < 2 ^ 64 -> 4096 <= fr + 32 -> fr + 40 <= 2 ^ 47 - 2 ^ 23 ->
  Z.of_nat (length txt) = n -> 0 <= cc <= n -> 4096 <= res -> res + n + 1 <= 2 ^ 47 - 2 ^ 23 ->
  Forall (fun c => numch c = true) txt ->
  (v + 16 <= q \/ q + 8 <= v) -> (res + n + 1 <= v \/ v + 16 <= res) ->
  val_mem segs (rdW W mem) (fr + 32) 8 (res + cc) -> garr8 segs (rdW W mem) res (txt ++ [0]) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 24 -> amem_range v 24 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 8 -> amem_range q 8 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF res (n + 1) -> amem_range res (n + 1) ->
  (forall a, v <= a < v + 16 ->
     awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly S) ly
       [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly a) ->
  (forall a, q <= a < q + 8 ->
     awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly S) ly
       [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly a) ->
  (* row 326, refused at row 311 (the token not consumed whole) or at row 315 (not finite) *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k ->
     vne_kept regs' regs -> getr regs' 21 = getr regs 21 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 8 <= a < v + 16) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     val_mem segs (rdW W mem') (v + 8) 8 bits ->
     ((cc =? n) && finite bits)%bool = false ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  (* row 326, accepted *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k ->
     vne_kept regs' regs -> getr regs' 21 = w64 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> ~ (v + 8 <= a < v + 16) -> ~ (q <= a < q + 8) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     val_mem segs (rdW W mem') v 4 3 -> val_mem segs (rdW W mem') (v + 8) 8 bits ->
     val_mem segs (rdW W mem') q 8 s6 ->
     cc = n -> finite bits = true ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 299) regs mem md) Q.
Proof.
intros d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md fr res cc n s6 bits txt Q HJ.
intros R19 R20 R22 R23 R25 R27 FA0 Hv0 Hv8 Hv1 Hq0 Hq8 Hq1 Hs6 Hf0 Hf1 Hlen Hcc Hr0 Hr1 HNUM Dvq Drv
  VE GT RAv Amv RAq Amq RAr Amr HWN HWQ HREF HACC.
apply (vne_seg_299_P B ARx SK LAWS (fun _ => True) vne_true_laws d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
  W regs mem md fr res cc n s6 bits txt Q HJ I R19 R20 R22 R23 R25 R27 FA0 Hv0 Hv8 Hv1 Hq0 Hq8 Hq1 Hs6 Hf0 Hf1 Hlen Hcc
  Hr0 Hr1 HNUM Dvq Drv VE GT RAv Amv RAq Amq RAr Amr HWN HWQ).
- intros regs' mem' md' HJ' _. exact (HREF regs' mem' md' HJ').
- intros regs' mem' md' HJ' _. exact (HACC regs' mem' md' HJ').
Qed.
End mt.

(* ======================================================================================================== *)
(* PART B: THE END SEGMENT, from VnumF's boundary vrd_num299_a (row 299) to the shared join at row 225       *)
(* ======================================================================================================== *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B prh_pst ARx).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

(* THE END SEGMENT'S STATEMENT (the form VnumF's vrd_num_tail binds; generic in the memory invariant P, a Theorem Labs lane's
   12:18Z template: an SRr post is opaque once Qed, so the end state's invariant is in the statement) *)
Definition vrd_num_end_stmt : Prop :=
  forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    (W : world segs) (c : config),
  vrd_num299_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    W c ->
  P (ms_mem (cfg_ms c)) ->
  SRr segs W c
    (fun W' c' => (exists (fx2 : YK11.FPState) (pos rv : Z),
       vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
         (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv)
         W' c') /\ P (ms_mem (cfg_ms c'))).

Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
(* instance facts: the harness head is at least one word wide (the kit's prh_head_wide; a Theorem Labs lane's preset_head_wide,
   lib/A/CfParamsPreset.v:95), and alloc.c's statics are image bytes (S1ImgA.v pst_in_img_A at prh_img_A) *)
Hypothesis HW : prh_head_wide.
Hypothesis H_pst_img : forall a, Exists (in_zr a) prh_pst -> in_img segs a.

Local Ltac vne_in3 := cbn [vne_kl In]; repeat (first [left; reflexivity | right]).
(* a saved word's byte is not a node byte: the node is outside the stack window (prhPv_node) *)
Local Ltac vne_nstk KSTK := match goal with |- ~ (_ <= ?a < _) => let Hx := fresh "Hx" in intros Hx; apply (KSTK a); lia end.

(* ---- THE NODE APART: the node lies in an entry block or an entry fake frame (prhReader_at; not in the granted
   window), so the allocator's separation at the current state puts it apart from the new block N, from this call's
   own fake frame, and from every harness head (its own block's head lies below it: HW); it is no image byte, and it
   lies below the allocator ceiling ---- *)
Lemma vne_sep : forall ly0 S0 Hp0 (W0 : world segs) mem0 md0 ly2 S2 Hp2 (W : world segs) mem md
    (Lam : list (Z * Z)) peak cnt fail ran most own regs0 e v pos N,
  ARx ly0 S0 Hp0 W0 mem0 md0 -> ARx ly2 S2 Hp2 W mem md ->
  layout_le (length (st_secs S0)) ly0 ly2 ->
  ablocks B ly2 S2 = ablocks B ly0 S0 ++ [N] -> frames S2 = (0, pos) :: frames S0 ->
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran most own ->
  prhReader_at B ly0 S0 Lam regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  (fst N + req_size (snd N) <= v \/ v + 56 <= fst N) /\
  (frame_addr ly2 0 pos + fs_frame_bytes 0 <= v \/ v + 56 <= frame_addr ly2 0 pos) /\
  (forall h k, In (h, k) Lam -> h - cf_head + 8 <= v \/ v + 56 <= h - cf_head) /\
  (forall a, v <= a < v + 56 -> ~ in_img segs a) /\
  v + 56 <= alloc_ceiling.
Proof.
intros ly0 S0 Hp0 W0 mem0 md0 ly2 S2 Hp2 W mem md Lam peak cnt fail ran most own regs0 e v pos N
  HAR0 HAR2 HLE EAB EFR HLD HAT HWN0.
pose proof cf_head_nonneg as Hch. pose proof HW as HW8. unfold prh_head_wide in HW8.
destruct (alx_layout segs B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 ly2 HAR0 HLE) as (_ & HFA & _).
destruct (alx_sep segs B ARx LAWS ly2 S2 Hp2 W mem md HAR2) as [HPW _].
destruct (alx_sep segs B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 HAR0) as [_ HFB0].
rewrite EAB, EFR, map_app in HPW. cbn [map] in HPW. rewrite <- app_assoc in HPW. cbn [app] in HPW.
assert (HMF : map (fun f : Z * Z => (frame_addr ly2 (fst f) (snd f), fs_frame_bytes (fst f))) (frames S0) =
              map (fun f : Z * Z => (frame_addr ly0 (fst f) (snd f), fs_frame_bytes (fst f))) (frames S0))
  by (apply map_ext; intros [cid ps]; cbn [fst snd]; rewrite HFA; reflexivity).
rewrite HMF in HPW.
(* the pairs the argument reads *)
assert (H1 : forall x, In x (ablocks B ly0 S0) -> zdisjoint (fst x, req_size (snd x)) (fst N, req_size (snd N)))
  by (intros x Hx; exact (vne_pw_app _ _ _ _ HPW (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ x Hx)
        (in_eq _ _))).
assert (H2 : forall x, In x (ablocks B ly0 S0) ->
          zdisjoint (fst x, req_size (snd x)) (frame_addr ly2 0 pos, fs_frame_bytes 0))
  by (intros x Hx; exact (vne_pw_app _ _ _ _ HPW (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ x Hx)
        (in_cons _ _ _ (in_eq _ _)))).
assert (H3 : forall x f, In x (ablocks B ly0 S0) -> In f (frames S0) ->
          zdisjoint (fst x, req_size (snd x)) (frame_addr ly0 (fst f) (snd f), fs_frame_bytes (fst f)))
  by (intros x f Hx Hf; exact (vne_pw_app _ _ _ _ HPW (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ x Hx)
        (in_cons _ _ _ (in_cons _ _ _
           (in_map (fun f : Z * Z => (frame_addr ly0 (fst f) (snd f), fs_frame_bytes (fst f))) _ f Hf))))).
assert (H4 : forall f, In f (frames S0) ->
          zdisjoint (fst N, req_size (snd N)) (frame_addr ly0 (fst f) (snd f), fs_frame_bytes (fst f)) /\
          zdisjoint (frame_addr ly2 0 pos, fs_frame_bytes 0)
            (frame_addr ly0 (fst f) (snd f), fs_frame_bytes (fst f))).
{ intros f Hf. apply pairwise_app_l in HPW as [_ HT]. destruct HT as [HF1 [HF2 _]].
  pose proof (in_map (fun f : Z * Z => (frame_addr ly0 (fst f) (snd f), fs_frame_bytes (fst f))) _ f Hf) as Hm.
  rewrite Forall_forall in HF1, HF2. split; [exact (HF1 _ (in_cons _ _ _ Hm)) | exact (HF2 _ Hm)]. }
assert (H5 : forall x y, In x (ablocks B ly0 S0) -> In y (ablocks B ly0 S0) -> x <> y ->
          zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y)))
  by (intros x y Hx Hy Hne; exact (vne_pw_map2 (fun b : Z * Z => (fst b, req_size (snd b))) _ _ x y HPW Hx Hy Hne)).
assert (HRQ : forall k0, 0 <= k0 -> req_size (k0 + cf_head) = k0 + cf_head)
  by (intros k0 Hk0; unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
assert (HHD : forall h k0, In (h, k0) Lam -> 0 <= k0 /\ In (h - cf_head, k0 + cf_head) (ablocks B ly0 S0)).
{ intros h k0 Hin. destruct (prh_ledger_hblock B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran h k0 most own HLD Hin)
    as (Hk & Hab & _). split; assumption. }
destruct HAT as [(a' & k' & Hin' & Ha1 & Ha2) | [(b & m & Hin & Hnot & Hb1 & Hb2) |
                [(cid & ps & Hin & Hf1 & Hf2) | (Hw1 & Hw2)]]].
- (* a harness block's user bytes *)
  destruct (HHD a' k' Hin') as (Hk' & Hab'). pose proof (HRQ k' Hk') as Hr'.
  pose proof (H1 _ Hab') as D1. pose proof (H2 _ Hab') as D2.
  unfold zdisjoint in D1, D2. cbn [fst snd] in D1, D2. rewrite Hr' in D1, D2.
  destruct (alx_blocks segs B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 _ _ HAR0 Hab') as (_ & _ & Hc' & _).
  rewrite Hr' in Hc'.
  split; [lia|]. split; [lia|]. split.
  + intros h k0 Hin. destruct (Z.eq_dec h a') as [->|Hne]; [left; lia|].
    destruct (HHD h k0 Hin) as (Hk0 & Hab).
    pose proof (H5 _ _ Hab Hab' ltac:(intros E; injection E; lia)) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite (HRQ k0 Hk0), Hr' in D. lia.
  + split; [|lia].
    intros a Ha. refine (proj2 (alx_client_img segs B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 a HAR0 _)).
    left. exists (a' - cf_head), (k' + cf_head). split; [exact Hab' | rewrite Hr'; lia].
- (* an allocator block that is not a harness block *)
  assert (Hrm : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  pose proof (H1 _ Hin) as D1. pose proof (H2 _ Hin) as D2.
  unfold zdisjoint in D1, D2. cbn [fst snd] in D1, D2. rewrite Hrm in D1, D2.
  destruct (alx_blocks segs B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 _ _ HAR0 Hin) as (_ & _ & Hc & _).
  rewrite Hrm in Hc.
  split; [lia|]. split; [lia|]. split.
  + intros h k0 Hin2. destruct (HHD h k0 Hin2) as (Hk0 & Hab).
    assert (Hne : (h - cf_head, k0 + cf_head) <> (b, m)).
    { intros E. injection E as E1 E2. apply Hnot.
      replace (b + cf_head) with h by lia. replace (m - cf_head) with k0 by lia. exact Hin2. }
    pose proof (H5 _ _ Hab Hin Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
    rewrite (HRQ k0 Hk0), Hrm in D. lia.
  + split; [|lia].
    intros a Ha. refine (proj2 (alx_client_img segs B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 a HAR0 _)).
    left. exists b, m. split; [exact Hin | rewrite Hrm; lia].
- (* an entry fake frame *)
  destruct (H4 _ Hin) as [D1 D2]. unfold zdisjoint in D1, D2. cbn [fst snd] in D1, D2.
  rewrite Forall_forall in HFB0. pose proof (HFB0 _ Hin) as Hc. cbn [fst snd] in Hc.
  split; [lia|]. split; [lia|]. split.
  + intros h k0 Hin2. destruct (HHD h k0 Hin2) as (Hk0 & Hab).
    pose proof (H3 _ _ Hab Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. rewrite (HRQ k0 Hk0) in D. lia.
  + split; [|lia].
    intros a Ha. refine (proj2 (alx_client_img segs B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 a HAR0 _)).
    right. left. exists cid, ps. split; [exact Hin | lia].
- (* the granted window: excluded by rd_pre *)
  exfalso. lia.
Qed.

(* the join at fx2 re-pinned to the entry float state: only vrd_epi_a's fregs_kept_x reads the Section's fx *)
Lemma vne_epi_repin : forall (fx2 : YK11.FPState) d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ (W : world segs) c,
  fregs_kept_x fx fx2 ->
  vrd_epi_a (fx := fx2) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c ->
  vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c.
Proof.
intros fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c FK
  (regs & mem & md & ly & S & Hp & k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & _
   & H16).
exists regs, mem, md, ly, S, Hp, k.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
  (conj H12 (conj H13 (conj H14 (conj FK H16))))))))))))))).
Qed.

(* ---- THE END SEGMENT: VnumF's boundary at row 299, the machine segment (vne_seg_299_P at strtod's float state),
   the arm's result vrd_pv_post at row 326 for both exits, the refusal join rows 326..328 (VrdRefJoinP.vrd_ref_join_P),
   and the join re-pinned to the entry float state. The model: vrd_num_tok gives txt, the one allocation of |txt| + 1
   bytes is the trace [EAlloc (S |txt|)] at ok = [true], and whole txt is the two machine tests (rows 311, 315). ---- *)
Theorem vrd_num_end : vrd_num_end_stmt.
Proof.
unfold vrd_num_end_stmt.
intros P PLAW ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
  W c H299 HPc.
destruct H299 as (fx2 & Wd & pos & p' & k1 & k & lyd & ly2 & Sd & S2 & Hpd & Hp2 & regs1 & mem1 & md1 & regs & mem & md &
  txt & r & res & bits & cc & sp & fr & -> & FZ2 & FK2 & HPRE & R10q & R11v & HRD & HB & Htok & Hr & Hcf & Hres0 &
  Hres16 & Hresn & EHp2 & EAB2 & HRL2 & HHU2 & HLED2 & HJ & EFR2 & HWIN & Hsm & Hcc & FA0 & VE & Efr & Efr' & R2 & R9 & R8 &
  R18 & R26 & R24 & R25 & R19 & R20 & R23 & R27 & R21 & R22 & R3 & R4 & Hsp & Hsp32 & Hsp16 & V16 & GT & VF0 & VF16 &
  VF56 & HSAV & RAv & RAq & RAr & HIN & HRW & HZ & HTR & HLV & HWN).
change (P mem) in HPc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HKLS : kLowShadowBeg = 2147446784) by reflexivity.
pose proof cf_head_nonneg as Hch. pose proof HW as HW8. unfold prh_head_wide in HW8.
pose proof (vrd_stk_big d) as HSTK.
destruct HPRE as ((HAR0 & Hret & _ & _ & _ & HASTK & _) & _).
destruct HASTK as (_ & _ & Hclo & Hlo & Hhi & H47 & _ & Htop1 & Htop2).
destruct HRD as (_ & _ & _ & _ & _ & HFW0 & Hq0 & Hq1 & _ & HSRC0 & _ & HMR & HNODE0 & Dqv & Dtv & Dwv & HLED0 & Hd &
  Hcnt & _).
destruct HNODE0 as (Hv0 & Hv8 & _ & _ & HAT & Hamv & HNSTK & _).
destruct HFW0 as (He0 & _ & Hetop & _).
destruct HSRC0 as (_ & Ht4096 & Htceil & Hamt & _).
pose proof HIN as (Vq & Vq8 & Vq16 & Hrwq & Hq8 & Ht0 & Htl & Hp'r & Hlen & GTt & Dqt & Hd32).
rewrite Hlen in Htceil, Hamt.
pose proof HB as (HRest & _ & HM & _ & _ & HAB & _).
pose proof HJ as (HAR2 & HLE & _).
(* the count's range, read out of prh_glob without positions (the kit's Batch 2 inserts a cell into prh_glob) *)
assert (HGL : 0 <= cnt < 2 ^ 64)
  by (destruct HLED0 as (HG0 & _); unfold prh_glob in HG0; decompose [and] HG0; lia).
(* the token and its lengths *)
destruct (vne_tok_spec _ _ _ Htok) as (Etok & HNUM & Hn1).
pose proof (vne_txt_len tb text p' txt r Etok HNUM) as Hmr.
pose proof (vne_bits_range txt bits cc Hsm) as Hbits.
assert (HLr' : Z.of_nat (length (rest_atR tb text p')) = len - (p' - text))
  by (unfold rest_atR; rewrite length_skipn; lia).
assert (HLe : length (rest_atR tb text p') = (length txt + length r)%nat) by (rewrite Etok, length_app; reflexivity).
assert (HLp : (length (rest_atR tb text p') <= length (rest_atR tb text p))%nat)
  by (rewrite HRest; apply PjGrammar.skip_len).
set (n := Z.of_nat (length txt)) in *.
assert (Hn : n = Z.of_nat (length txt)) by reflexivity. clearbody n.
assert (Hpn : p' + n + Z.of_nat (length r) = text + len) by lia.
(* the model: jr_value at ok = [true] *)
destruct (PjGrammar.skip (rest_atR tb text p)) as [|b y] eqn:Esk; [destruct HM as [Hc _]; discriminate Hc|].
destruct HM as (Harm & _).
assert (HR : rest_atR tb text p' = b :: y) by (first [exact HRest | rewrite HRest; exact Esk]).
assert (N6 : b <> 123 /\ b <> 91 /\ b <> 34 /\ b <> 116 /\ b <> 102 /\ b <> 110).
{ unfold vrd_arm_of in Harm. repeat split; intros Hb; subst b; cbn in Harm; discriminate Harm. }
assert (Eb : snd (prh_jr_strtod txt) = bits /\ fst (prh_jr_strtod txt) = cc)
  by (unfold vrd_sm in Hsm; injection Hsm as E1 E2; split; assumption).
assert (HJV : jr_value prh_jr_strtod d (rest_atR tb text p) [true] =
  (if ((cc =? n) && finite bits)%bool then (Some (JNum txt bits, r), [EAlloc (S (length txt))], [])
   else (None, [EAlloc (S (length txt))], []))).
{ destruct N6 as (N1 & N2 & N3 & N4 & N5 & N6).
  rewrite (vrd_jr_value_number prh_jr_strtod d (rest_atR tb text p) b y [true] Esk N1 N2 N3 N4 N5 N6).
  rewrite vrd_num_tok_spec, <- HR, Htok. cbn [take]. unfold whole. destruct Eb as [-> ->]. rewrite <- Hn.
  reflexivity. }
(* the ALL-GRANTED run (ok = []) gives the same answer and trace, so prhPv_gtrace is the instance's trace (the
   outcome clause's granted run) *)
assert (HJV0 : jr_value prh_jr_strtod d (rest_atR tb text p) [] = jr_value prh_jr_strtod d (rest_atR tb text p) [true]).
{ destruct N6 as (N1 & N2 & N3 & N4 & N5 & N6).
  rewrite (vrd_jr_value_number prh_jr_strtod d (rest_atR tb text p) b y [] Esk N1 N2 N3 N4 N5 N6).
  rewrite (vrd_jr_value_number prh_jr_strtod d (rest_atR tb text p) b y [true] Esk N1 N2 N3 N4 N5 N6).
  rewrite !vrd_num_tok_spec, <- HR, Htok. reflexivity. }
assert (HGT : prhPv_gtrace d (rest_atR tb text p) = [EAlloc (S (length txt))]).
{ unfold prhPv_gtrace. rewrite HJV0, HJV. destruct ((cc =? n) && finite bits)%bool; reflexivity. }
(* the node apart from the new block, this call's frame, the heads; the new block's place *)
assert (EAB2' : ablocks B ly2 S2 = ablocks B ly0 S0 ++ [(res - cf_head, n + 1 + cf_head)])
  by (rewrite EAB2, HAB; reflexivity).
destruct (vne_sep ly0 S0 Hp0 W0 mem0 md0 ly2 S2 Hp2 W mem md Lam peak cnt fail ran most own regs0 e v pos _ HAR0 HAR2
  HLE EAB2' EFR2 HLED0 HAT Dwv) as (SN & SF & SH & SI & SC).
assert (Hrq : req_size (n + 1 + cf_head) = n + 1 + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (n + 1 + cf_head) 0); lia).
cbn [fst snd] in SN. rewrite Hrq in SN.
assert (HinN : In (res - cf_head, n + 1 + cf_head) (ablocks B ly2 S2))
  by (rewrite EAB2'; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W mem md _ _ HAR2 HinN) as (_ & HN4096 & HNc & HNapp & _).
rewrite Hrq in HNc, HNapp.
destruct (alx_sep segs B ARx LAWS ly2 S2 Hp2 W mem md HAR2) as [HPW2 HFB2].
pose proof HFB2 as HFB2'. rewrite EFR2 in HFB2'. apply Forall_inv in HFB2'. cbn [fst snd] in HFB2'.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in HFB2', SF. rewrite <- Efr in HFB2', SF.
assert (HNEW : ~ In (res - cf_head, n + 1 + cf_head) (ablocks B ly0 S0)).
{ intros Hin. rewrite EAB2', map_app in HPW2. apply pairwise_app_l in HPW2 as [HPB _]. cbn [map] in HPB.
  pose proof (vne_pw_app _ _ _ _ HPB (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ _ Hin) (in_eq _ _))
    as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hrq in D. lia. }
assert (HLB : forall h k0, In (h, k0) Lam -> 4096 <= h - cf_head /\ h - cf_head + 8 <= alloc_ceiling).
{ intros h k0 Hin. destruct (prh_ledger_hblock B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran h k0 most own HLED0 Hin)
    as (Hk & Hab & _).
  destruct (alx_blocks segs B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 _ _ HAR0 Hab) as (_ & H4 & Hc & _).
  assert (req_size (k0 + cf_head) = k0 + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
  lia. }
assert (KSTK : forall a, spZ regs0 - 104 <= a < spZ regs0 -> ~ (v <= a < v + 56)).
{ intros a Ha Hx. destruct (HNSTK a Hx) as [_ Hns]. apply Hns. lia. }
assert (Amq : amem_range q 8) by (unfold amem_range; right; lia).
assert (Amr : amem_range res (n + 1)).
{ unfold amem_range. unfold in_app in HNapp. destruct HNapp as (_ & [Hlow | [Hh1 _]]); [left | right]; lia. }
assert (HWQ : forall a, q <= a < q + 8 ->
   awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly2 S2) ly2
     [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly2 a).
{ intros a Ha. left. left. lia. }
(* the ledger move (PRH_FnParse.rd_ledger_move, #102 form: most, the all-granted trace, the refusal peak) *)
assert (HPK : 0 <= peak) by (destruct HLED0 as (HG0 & _); unfold prh_glob in HG0; decompose [and] HG0; lia).
assert (HLM : rd_ledger_move Lam peak cnt fail ran most [true] (prhPv_gtrace d (rest_atR tb text p))
               [EAlloc (S (length txt))] [(res, n + 1)]
               ((res, n + 1) :: Lam) (Z.max peak (Ledger.lsum Lam + (n + 1))) ((cnt + 1) mod 2 ^ 64) fail ran).
{ pose proof (vle_alloc Lam peak cnt fail ran most (prhPv_gtrace d (rest_atR tb text p)) res (S (length txt))
    ltac:(lia) ltac:(lia) Hcf HPK) as HLM.
  replace (Z.of_nat (S (length txt))) with (n + 1) in HLM by lia.
  replace (cnt + 1) with ((cnt + 1) mod 2 ^ 64) in HLM by (apply Z.mod_small; lia). exact HLM. }
assert (HPERM : Permutation (ablocks B ly2 S2) (prhReader_ab [(res, n + 1)] ++ ablocks B ly0 S0)).
{ rewrite EAB2'. unfold prhReader_ab. cbn [map fst snd app]. symmetry. apply Permutation_cons_append. }
assert (HHP : hpeakR [EAlloc (S (length txt))] <=
              224 * Z.of_nat (length (rest_atR tb text p)) + 512 * Z.of_nat (PjGrammar.MAXD - d))
  by (cbn [hpeakR PjGrammar.held_ev]; lia).
assert (HBB : blocks_bytes S2 <= blocks_bytes S0 + prh_held [EAlloc (S (length txt))]).
{ rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly0 S0), EAB2', bsum_app. unfold prh_held.
  cbn [bsum fold_right snd PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]. lia. }
assert (HLS : Ledger.lsum [(res, n + 1)] = PjGrammar.held [EAlloc (S (length txt))])
  by (unfold Ledger.lsum; cbn; lia).
(* the machine segment *)
refine (vne_seg_299_P (fx := fx2) B ARx SK LAWS P PLAW d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly2 S2 Hp2 k W regs
  mem md fr res cc n (p' + n) bits txt _ HJ HPc R19 R20 R22 R23 R25 R27 FA0 Hv0 Hv8 ltac:(lia) ltac:(lia) Hq8
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (eq_sym Hn) Hcc ltac:(lia) ltac:(lia) HNUM ltac:(lia) ltac:(lia) VE GT
  RAv (vrd_amem_sub v 56 v 24 Hamv ltac:(lia) ltac:(lia) ltac:(lia)) RAq Amq RAr Amr HWN HWQ _ _).
- (* ===== row 326, refused (rows 311 / 315 taken): rv = -1 ===== *)
  intros regs' mem' md' HJ' HPM' HK' R21' KEEP MG VB Hwh.
  assert (KW : forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a -> ~ (v + 8 <= a < v + 16)).
  { intros a _ Hn' Hx. apply Hn'. exists (v, v + 56). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
  assert (HRQ : vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos (-1) ly2 S2 Hp2 W mem').
  { unfold vrd_pv_post.
    exists [true], None, [EAlloc (S (length txt))], [], [(res, n + 1)], ((res, n + 1) :: Lam),
      (Z.max peak (Ledger.lsum Lam + (n + 1))), ((cnt + 1) mod 2 ^ 64), fail, ran.
    split; [change ReaderRes.jr_strtod with prh_jr_strtod; rewrite HJV, Hwh; reflexivity|].
    split.
    { apply (prh_ledger_kept_aview B ly2 S2 Hp2 W mem ly2 S2 Hp2 W mem' _ _ _ _ _ _ _ HLED2).
      - intros a Ha. pose proof (H_pst_img a Ha) as Himg.
        pose proof (@pa_segs_low _ A_prog_listing PI_prog_A a Himg) as Hlo'.
        apply KEEP; [lia|]. intros Hx. exact (SI a ltac:(lia) Himg).
      - intros h k0 i Hin Hi. destruct Hin as [E | Hin].
        + injection E as <- <-. apply KEEP; lia.
        + pose proof (HLB h k0 Hin). pose proof (SH h k0 Hin). apply KEEP; lia.
      - intros a k0 _ H. exact H.
      - apply Permutation_refl. }
    split; [exact HRL2|]. split; [rewrite HGT; exact HHU2|]. split; [exact HLV|]. split; [exact HTR|].
    split.
    { intros sm x os i H0 hist Hpos Hrun _ _. rewrite HGT in Hrun |- *.
      split; [reflexivity|]. split; [|exact (HTR sm x os i H0 hist Hpos Hrun)].
      change ReaderRes.jr_strtod with prh_jr_strtod. rewrite HJV0, HJV, Hwh. reflexivity. }
    (* THE OUTCOME OF AN INJECTED READING: the one outcome was a grant (ok = [true]), so none failed *)
    split; [intros sm x os i H0 hist _ _ _ _ ii Hii Hf; destruct ii as [|ii]; [cbn in Hf; discriminate Hf | cbn in Hii; lia]|].
    split; [exact HLM|].
    split; [intros a k0 Hin; destruct Hin as [E | []]; injection E as <- <-; exact HNEW|].
    split; [exact HPERM|]. split; [rewrite EFR2; apply Permutation_refl|].
    split; [exact HHP|]. split; [exact HBB|]. split; [exact HLS|].
    split; [reflexivity|].
    (* the node's header after the refusal: type and kids / keys / n / cap still 0, num = bits, str = the kept block
       (the token copy is the node's string, PresetReqAt.lf's one block) *)
    assert (HHD : pj_hdrR segs (rdW W mem') v 0 bits res 0 0 0 0).
    { destruct HRW as [_ HRWv].
      split; [split; [exact Hv8 | intros x Hx; exact (writable_at_grows segs _ _ x MG (HRWv x Hx))]|].
      split; [split; [lia | apply vne_val0; intros i Hi; cbn in Hi; rewrite KEEP by lia; apply HZ; lia]|].
      split; [split; [exact Hbits | exact VB]|].
      split; [split; [lia | eapply val_mem_kept; [|exact V16]; intros kk Hk; cbn in Hk; apply KEEP; lia]|].
      split; [split; [lia | apply vne_val0; intros i Hi; cbn in Hi; rewrite KEEP by lia; apply HZ; lia]|]. split; [split; [lia | apply vne_val0; intros i Hi; cbn in Hi; rewrite KEEP by lia; apply HZ; lia]|]. split; [split; [lia | apply vne_val0; intros i Hi; cbn in Hi; rewrite KEEP by lia; apply HZ; lia]|]. split; [lia | apply vne_val0; intros i Hi; cbn in Hi; rewrite KEEP by lia; apply HZ; lia]. }
    assert (HAP : pj_apartR [(res, n + 1)] v)
      by (intros b0 x Hb Hx; destruct Hb as [<- | []]; unfold pj_holdsR in Hx; cbn [fst snd] in Hx; lia).
    (* THE FREE ORDER (the kit's cut, FREEORD-NONE): the one block, the node's str, at every depth (VrdNum.vrd_str_fo);
       the model's list is the leaf's of the trace [EAlloc (S |txt|)] (VrdNum.vrd_frees_leaf) *)
    split.
    { intros HH nn _. exists [(res, n + 1)]. split.
      - apply (vrd_str_fo segs _ _ nn v 0 bits res (n + 1) HHD); [left; reflexivity | exact HAP].
      - rewrite (vrd_frees_leaf d (rest_atR tb text p) [true] b y Esk (proj1 N6) (proj1 (proj2 N6))).
        change ReaderRes.jr_strtod with prh_jr_strtod. rewrite HJV, Hwh.
        cbn [map fst snd PresetReqAt.lf]. f_equal. rewrite HH. lia. }
    split.
    { exists p', (Z.of_nat d). split; [lia|]. split; [lia|].
      split; [eapply val_mem_kept; [|exact Vq]; intros kk Hk; cbn in Hk; apply KEEP; lia|].
      split; [eapply val_mem_kept; [|exact Vq8]; intros kk Hk; cbn in Hk; apply KEEP; lia|].
      split; [eapply val_mem_kept; [|exact Vq16]; intros kk Hk; cbn in Hk; apply KEEP; lia|].
      intros x Hx. apply (writable_at_grows segs _ _ x MG). exact (Hrwq x Hx). }
    apply (vne_fd_str segs _ _ _ v 0 bits res (n + 1) HHD); [left; reflexivity | exact HAP]. }
  assert (Href : vrd_ref_a (fx := fx2) B ARx SK d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos (-1)
                   (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos (-1))
                   W (cfg_at (fx := fx2) segs (BASE + vrd_row 326) regs' mem' md')).
  { exists regs', mem', md', ly2, S2, Hp2, k.
    split; [first [rewrite <- vrd_pc_ref; reflexivity | unfold cfg_at; rewrite <- vrd_pc_ref; reflexivity
            | unfold cfg_at; f_equal; f_equal; vm_compute; reflexivity]|].
    split; [exact HJ'|].
    split; [intros a Ha Hn'; rewrite KEEP by (first [exact (KW a Ha Hn') | lia]); exact (HWIN a Ha Hn')|].
    split; [rewrite (HK' 8%bv) by vne_in3; exact R8|].
    split; [rewrite (HK' 18%bv) by vne_in3; rewrite R18, Efr; reflexivity|].
    split; [rewrite (HK' 26%bv) by vne_in3; rewrite R26, Efr; reflexivity|].
    split; [rewrite (HK' 24%bv) by vne_in3; rewrite R24, Efr; reflexivity|].
    split; [rewrite R21'; exact R21|].
    split; [rewrite (HK' 3%bv) by vne_in3; exact R3|].
    split; [rewrite (HK' 4%bv) by vne_in3; exact R4|].
    split; [exact Hret|].
    split.
    { unfold vrd_saved in HSAV |- *.
      destruct HSAV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split; (eapply val_mem_kept; [|eassumption]); intros kk Hk; cbn in Hk;
        (apply KEEP; [lia | vne_nstk KSTK]). }
    split; [rewrite <- Efr; eapply val_mem_kept; [|exact VF56]; intros kk Hk; cbn in Hk; apply KEEP; lia|].
    split; [rewrite EFR2; left; reflexivity|].
    split; [exact FZ2|].
    split; [lia|].
    exact HRQ. }
  eapply SRr_mono.
  + refine (vrd_ref_join_P (fx := fx2) B ARx SK LAWS P PLAW d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos (-1) _ W _ _
      Href _).
    * apply (vrd_pv_post_sh_frame B ARx LAWS); [exact H_pst_img | lia | lia | lia | exact Hamv | exact Hamt].
    * exact HPM'.
  + intros W' c' _ [Hepi HP']. split; [|exact HP']. exists fx2, pos, (-1).
    exact (vne_epi_repin fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos (-1) _ W' c' FK2 Hepi).
- (* ===== row 326, accepted: rv = 0 ===== *)
  intros regs' mem' md' HJ' HPM' HK' R21' KEEP MG VT VB VQ Hccn Hfin.
  assert (Hwh : ((cc =? n) && finite bits)%bool = true) by (rewrite Hccn, Z.eqb_refl, Hfin; reflexivity).
  assert (KW : forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     ~ (v <= a < v + 4) /\ ~ (v + 8 <= a < v + 16) /\ ~ (q <= a < q + 8)).
  { intros a _ Hn'. split; [|split]; intros Hx; apply Hn'.
    - exists (v, v + 56). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
    - exists (v, v + 56). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
    - exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (HRQ : vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos 0 ly2 S2 Hp2 W mem').
  { unfold vrd_pv_post.
    exists [true], (Some (JNum txt bits, r)), [EAlloc (S (length txt))], [], [(res, n + 1)], ((res, n + 1) :: Lam),
      (Z.max peak (Ledger.lsum Lam + (n + 1))), ((cnt + 1) mod 2 ^ 64), fail, ran.
    split; [change ReaderRes.jr_strtod with prh_jr_strtod; rewrite HJV, Hwh; reflexivity|].
    split.
    { apply (prh_ledger_kept_aview B ly2 S2 Hp2 W mem ly2 S2 Hp2 W mem' _ _ _ _ _ _ _ HLED2).
      - intros a Ha. pose proof (H_pst_img a Ha) as Himg.
        pose proof (@pa_segs_low _ A_prog_listing PI_prog_A a Himg) as Hlo'.
        apply KEEP; [lia | intros Hx; exact (SI a ltac:(lia) Himg) | intros Hx; exact (SI a ltac:(lia) Himg) | lia].
      - intros h k0 i Hin Hi. destruct Hin as [E | Hin].
        + injection E as <- <-. apply KEEP; lia.
        + pose proof (HLB h k0 Hin). pose proof (SH h k0 Hin). apply KEEP; lia.
      - intros a k0 _ H. exact H.
      - apply Permutation_refl. }
    split; [exact HRL2|]. split; [rewrite HGT; exact HHU2|]. split; [exact HLV|]. split; [exact HTR|].
    split.
    { intros sm x os i H0 hist Hpos Hrun _ _. rewrite HGT in Hrun |- *.
      split; [reflexivity|]. split; [|exact (HTR sm x os i H0 hist Hpos Hrun)].
      change ReaderRes.jr_strtod with prh_jr_strtod. rewrite HJV0, HJV, Hwh. reflexivity. }
    split; [intros sm x os i H0 hist _ _ _ _ ii Hii Hf; destruct ii as [|ii]; [cbn in Hf; discriminate Hf | cbn in Hii; lia]|].
    split; [exact HLM|].
    split; [intros a k0 Hin; destruct Hin as [E | []]; injection E as <- <-; exact HNEW|].
    split; [exact HPERM|]. split; [rewrite EFR2; apply Permutation_refl|].
    split; [exact HHP|]. split; [exact HBB|]. split; [exact HLS|].
    split; [reflexivity|].
    (* the node's header: the number's tag, num = bits, str = the token copy, no kids / keys *)
    assert (HHD : pj_hdrR segs (rdW W mem') v (tag (JNum txt bits)) bits res 0 0 0 0).
    { destruct HRW as [_ HRWv].
      split; [split; [exact Hv8 | intros x Hx; exact (writable_at_grows segs _ _ x MG (HRWv x Hx))]|].
      split; [split; [cbn; lia | exact VT]|].
      split; [split; [exact Hbits | exact VB]|].
      split; [split; [lia | eapply val_mem_kept; [|exact V16]; intros kk Hk; cbn in Hk; apply KEEP; lia]|].
      split; [split; [lia | apply vne_val0; intros i Hi; cbn in Hi; rewrite KEEP by lia; apply HZ; lia]|]. split; [split; [lia | apply vne_val0; intros i Hi; cbn in Hi; rewrite KEEP by lia; apply HZ; lia]|]. split; [split; [lia | apply vne_val0; intros i Hi; cbn in Hi; rewrite KEEP by lia; apply HZ; lia]|]. split; [lia | apply vne_val0; intros i Hi; cbn in Hi; rewrite KEEP by lia; apply HZ; lia]. }
    assert (HAP : pj_apartR [(res, n + 1)] v)
      by (intros b0 x Hb Hx; destruct Hb as [<- | []]; unfold pj_holdsR in Hx; cbn [fst snd] in Hx; lia).
    (* THE FREE ORDER (the kit's cut, FREEORD-NONE): the number's one block, its str, at every depth *)
    split.
    { intros HH nn _. exists [(res, n + 1)]. split.
      - apply (vrd_str_fo segs _ _ nn v _ bits res (n + 1) HHD); [left; reflexivity | exact HAP].
      - rewrite (vrd_frees_leaf d (rest_atR tb text p) [true] b y Esk (proj1 N6) (proj1 (proj2 N6))).
        change ReaderRes.jr_strtod with prh_jr_strtod. rewrite HJV, Hwh.
        cbn [map fst snd PresetReqAt.lf]. f_equal. rewrite HH. lia. }
    split.
    { replace (text + len - Z.of_nat (length r)) with (p' + n) by lia.
      split; [exact VQ|].
      split; [eapply val_mem_kept; [|exact Vq8]; intros kk Hk; cbn in Hk; apply KEEP; lia|].
      split; [eapply val_mem_kept; [|exact Vq16]; intros kk Hk; cbn in Hk; apply KEEP; lia|].
      split; [intros x Hx; apply (writable_at_grows segs _ _ x MG); exact (Hrwq x Hx)|].
      split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [lia|]. split; [exact Hlen|].
      split; [apply (vrd_garr8_keep (w_H W) mem mem'); [|exact GTt]; intros j Hj; apply KEEP; lia|].
      split; [exact Dqt | exact Hd32]. }
    split.
    { cbn [pj_nodeR].
      split; [repeat constructor; intros Hc; inversion Hc|].
      split; [exact HAP|].
      exists bits, res, 0, 0, 0, 0.
      split; [exact HHD|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      exists (n + 1). split; [|reflexivity].
      split; [left; reflexivity|]. split; [lia|]. split; [lia|].
      split; [eapply Forall_impl; [|exact HNUM]; intros c0 Hc0; exact (vne_numch_rng c0 Hc0)|].
      apply (vrd_garr8_keep (w_H W) mem mem'); [|exact GT].
      intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. apply KEEP; lia. }
    (* CAP: a number is no container, pj_ncapR holds of it by computation *)
    split; [exact I|].
    rewrite HLS. cbn [PjGrammar.held PjGrammar.held_ev]. lia. }
  assert (Href : vrd_ref_a (fx := fx2) B ARx SK d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos 0
                   (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos 0)
                   W (cfg_at (fx := fx2) segs (BASE + vrd_row 326) regs' mem' md')).
  { exists regs', mem', md', ly2, S2, Hp2, k.
    split; [first [rewrite <- vrd_pc_ref; reflexivity | unfold cfg_at; rewrite <- vrd_pc_ref; reflexivity
            | unfold cfg_at; f_equal; f_equal; vm_compute; reflexivity]|].
    split; [exact HJ'|].
    split; [intros a Ha Hn'; destruct (KW a Ha Hn') as (KW1 & KW2 & KW3); rewrite KEEP by first [assumption | lia];
            exact (HWIN a Ha Hn')|].
    split; [rewrite (HK' 8%bv) by vne_in3; exact R8|].
    split; [rewrite (HK' 18%bv) by vne_in3; rewrite R18, Efr; reflexivity|].
    split; [rewrite (HK' 26%bv) by vne_in3; rewrite R26, Efr; reflexivity|].
    split; [rewrite (HK' 24%bv) by vne_in3; rewrite R24, Efr; reflexivity|].
    split; [exact R21'|].
    split; [rewrite (HK' 3%bv) by vne_in3; exact R3|].
    split; [rewrite (HK' 4%bv) by vne_in3; exact R4|].
    split; [exact Hret|].
    split.
    { unfold vrd_saved in HSAV |- *.
      destruct HSAV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split; (eapply val_mem_kept; [|eassumption]); intros kk Hk; cbn in Hk;
        (apply KEEP; [lia | vne_nstk KSTK | vne_nstk KSTK | lia]). }
    split; [rewrite <- Efr; eapply val_mem_kept; [|exact VF56]; intros kk Hk; cbn in Hk; apply KEEP; lia|].
    split; [rewrite EFR2; left; reflexivity|].
    split; [exact FZ2|].
    split; [lia|].
    exact HRQ. }
  eapply SRr_mono.
  + refine (vrd_ref_join_P (fx := fx2) B ARx SK LAWS P PLAW d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos 0 _ W _ _
      Href _).
    * apply (vrd_pv_post_sh_frame B ARx LAWS); [exact H_pst_img | lia | lia | lia | exact Hamv | exact Hamt].
    * exact HPM'.
  + intros W' c' _ [Hepi HP']. split; [|exact HP']. exists fx2, pos, 0.
    exact (vne_epi_repin fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos 0 _ W' c' FK2 Hepi).
Qed.

End e.

(* ======================================================================================================== *)
(* REAL-INSTANCE WITNESSES of the clauses this adaptation changed (VERIFY 21:4xZ check 1), at the real strtod  *)
(* model (ReaderRes.jr_strtod), #102's g_most (PjReqBound.PJ_ALLOC_BOUND) and the one-byte input [49]              *)
(* ======================================================================================================== *)
(* the input [49], the digit 1: one numch byte, so parse_value at d = 0 takes the number arm, one fuzz_malloc of
   |txt| + 1 = 2 *)
Definition vne_wx : list Z := [49].

(* the granted run: prhPv_gtrace is the one allocation, and ok = [] and ok = [true] give the same answer and trace
   (HJV0 / HGT's facts, and the outcome clause's `fst (jr_value .. []) = (res, tr)`, at the real model) *)
Lemma vne_wit_gtrace : prhPv_gtrace 0 vne_wx = [EAlloc 2].
Proof. vm_compute. reflexivity. Qed.

Lemma vne_wit_granted :
  fst (jr_value ReaderRes.jr_strtod 0 vne_wx []) = fst (jr_value ReaderRes.jr_strtod 0 vne_wx [true]) /\
  snd (fst (jr_value ReaderRes.jr_strtod 0 vne_wx [true])) = [EAlloc 2].
Proof. split; vm_compute; reflexivity. Qed.

(* HLM's move at the harness's start fields (g_live = g_peak = g_count = g_ran_out = 0), g_fail_at = 1 (no injected
   failure in the window: cnt + calls gt = 1 <= fail) and g_most = PJ_ALLOC_BOUND (|x|) (#102 fuzz_preset.c:810):
   vle_alloc's premises hold there, and its conclusion is the move HLM states (Lam' = [(x, 2)], peak' = 2,
   cnt' = 1, fail and ran kept) *)
Lemma vne_wit_move : forall x : Z,
  rd_ledger_move [] 0 0 1 0 (PjReqBound.PJ_ALLOC_BOUND (Z.of_nat (length vne_wx))) [true] (prhPv_gtrace 0 vne_wx)
    [EAlloc 2] [(x, 2)] [(x, 2)] (Z.max 0 (Ledger.lsum [] + 2)) ((0 + 1) mod 2 ^ 64) 1 0.
Proof.
  intros x.
  pose proof (vle_alloc [] 0 0 1 0 (PjReqBound.PJ_ALLOC_BOUND (Z.of_nat (length vne_wx))) (prhPv_gtrace 0 vne_wx) x
    2%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H.
  exact H.
Qed.

Print Assumptions vne_wit_granted.
Print Assumptions vne_wit_move.

Print Assumptions vrd_num_end.
