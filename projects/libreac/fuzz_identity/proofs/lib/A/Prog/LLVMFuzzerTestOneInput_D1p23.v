(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D1p56.v, with its module names changed; 396 of its 492 lines of code are new or changed and 645 lines of the source are left out. *)
(* Phases 2 and 3 of segment D1 of LLVMFuzzerTestOneInput's ASan walk (the cut is
   LLVMFuzzerTestOneInput_D1cut.v, which states d1_ph2_stmt and d1_ph3_stmt).

   Ph2 0x80bcc..0x80bf4: `mv s9,a0` keeps the payload copy's block pl, the NULL check of pl (refuted by
   4096 <= pl when k > 0), `sd s2,144(s1)` stores the length left after the header, and memcpy(pl, p + body, k)
   when k > 0 (0x80bf0). With k = 0 both branches jump to 0x80bf4 and the record's payload is empty.
   Ph3 0x80bf4..0x80c1c: the five shadow cells of `before` (SF+32, 38 bytes: four zero cells and a last cell 6,
   0x80bf4..0x80c04), the load of &id from mf+184 and memcpy(before, id, 38) (0x80c18).
   Both phases run the plain engine (IdentFrame's paj_run_shc / paj_run_to_shc: neither phase has an
   instrumented access, so no shadow token is needed) and take the copy from the __asan_memcpy contract
   AMEMCPY through YCbq's aj_intrin_at. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_D1cut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic states of the two phases ------------------------------------------------------------- *)
(* Ph2: only the machine frame's slot mf+144 is written; atom 10 is the malloc result and atom 22 the record's
   payload length, whose facts decide the NULL check and the two length branches. *)
Definition p2_mf : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 144 152 [].
Definition p2_facts : facts := mkFacts [(10%nat, mkAF 4096 140737479966720 0); (22%nat, mkAF 1 255 0)] [] [].
Definition ss_p2 (G : facts) : sstate := mkSS 0x4c0 sr_atoms [p2_mf] None G.

(* ---- list facts the payload copy needs ----------------------------------------------------------------- *)
Definition zz_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma dup2_split : forall (x : Z * Z) l, (2 <= count_occ zz_dec l x)%nat ->
  exists l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.
Proof.
intros x l. induction l as [|a l IH]; cbn [count_occ]; intros Hc; [lia|].
destruct (zz_dec a x) as [-> | Hne].
- assert (Hin : In x l) by (apply (count_occ_In zz_dec); lia).
  destruct (in_split x l Hin) as (l2 & l3 & ->). exists [], l2, l3. reflexivity.
- destruct (IH ltac:(lia)) as (l1 & l2 & l3 & ->). exists (a :: l1), l2, l3. reflexivity.
Qed.
Lemma p_nth_skipn : forall (l : list byte) o j d, nth j (skipn o l) d = nth (o + j) l d.
Proof.
intros l. induction l as [|b l IH]; intros [|o] j d; cbn [skipn nth Nat.add]; try reflexivity.
- destruct j; reflexivity.
- rewrite IH. reflexivity.
Qed.

Ltac p_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; unfold acallee_saved; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
(* What the two phases take, each with the name and type the contract's Section gives it. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
#[local] Notation CTX := (D1ctx B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation RUNS := (D1S B MT LLVMF_STK).
#[local] Notation NUMS := (d1_nums B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).
#[local] Notation AJ g pos ly3 S3 W3 mem3 md3 kk :=
  (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
     ly3 S3 W3 mem3 md3 kk).

(* ---- small facts the phases share ------------------------------------------------------------------------ *)
(* A byte of a byte array is present. *)
Lemma p_bytes_some : forall (W : world SEGS) m a (bs : list byte) j,
  bytes_at8 W m a bs -> (j < length bs)%nat -> aview SEGS (w_H W) m (a + Z.of_nat j) <> None.
Proof.
intros W m a bs j Hb Hj. unfold bytes_at8 in Hb.
pose proof (garr8_mbyte SEGS _ _ _ j Hb ltac:(rewrite length_map; exact Hj)) as Hm.
unfold aview. rewrite Hm. discriminate.
Qed.
(* A byte array copied to another address. *)
Lemma p_bytes_copied : forall (W : world SEGS) m m' a b (bs : list byte),
  (forall j, 0 <= j < Z.of_nat (length bs) -> aview SEGS (w_H W) m' (b + j) = aview SEGS (w_H W) m (a + j)) ->
  bytes_at8 W m a bs -> bytes_at8 W m' b bs.
Proof.
intros W m m' a b bs Heq Hb. unfold bytes_at8, garr8 in *. intros j Hj. rewrite length_map in Hj.
destruct (Hb j ltac:(rewrite length_map; exact Hj)) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W) m m' (a + Z.of_nat j) (b + Z.of_nat j) 1); [|exact Hv].
intros kk Hkk. assert (kk = 0) as -> by lia. rewrite !Z.add_0_r. apply Heq. lia.
Qed.
(* A slice of a byte array is a byte array. *)
Lemma p_bytes_sub : forall (W : world SEGS) m a (bs : list byte) (o n : nat),
  bytes_at8 W m a bs -> (o + n <= length bs)%nat ->
  bytes_at8 W m (a + Z.of_nat o) (firstn n (skipn o bs)).
Proof.
intros W m a bs o n Hb Hon. unfold bytes_at8, garr8 in *.
intros j Hj. rewrite length_map, length_firstn, length_skipn in Hj.
destruct (Hb (o + j)%nat ltac:(rewrite length_map; lia)) as [Hv Hr].
assert (En : nth j (map (fun b : byte => bv_unsigned b) (firstn n (skipn o bs))) 0
           = nth (o + j)%nat (map (fun b : byte => bv_unsigned b) bs) 0).
{ rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0)))
    by (rewrite length_map, length_firstn, length_skipn; lia).
  rewrite map_nth.
  rewrite (nth_indep (map (fun b : byte => bv_unsigned b) bs) 0 (bv_unsigned (RcIdentModel.zb 0)))
    by (rewrite length_map; lia).
  rewrite map_nth. f_equal. rewrite SlotModel.nth_first by lia. apply p_nth_skipn. }
rewrite En. split; [|exact Hr].
replace (a + Z.of_nat o + Z.of_nat j) with (a + Z.of_nat (o + j)) by lia. exact Hv.
Qed.
(* The input block's bytes hold at every state of the journal: the walk's FP is empty and the block is live
   at the entry and at the state. *)
Lemma p_in_bytes : forall g pos ly2 S2 (W2 : world SEGS) mem2 md2 ly3 S3 (W3 : world SEGS) mem3 md3 k2 k3,
  AJ g pos ly2 S2 W2 mem2 md2 k2 -> AJ g pos ly3 S3 W3 mem3 md3 k3 ->
  In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)) ->
  In (e_p g, e_n g) (ablocks B ly2 S2) -> In (e_p g, e_n g) (ablocks B ly3 S3) ->
  SlotModel.nlen (e_pl g) = e_n g -> 0 < e_n g ->
  bytes_at8 W2 mem2 (e_p g) (e_pl g) -> bytes_at8 W3 mem3 (e_p g) (e_pl g).
Proof.
intros g pos ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 k2 k3 HJ2 HJ3 Hin0 Hin2 Hin3 Hlen Hn Hb.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
unfold SlotModel.nlen in Hlen.
unfold bytes_at8 in *. apply (garr8_frame SEGS _ _ _ _ Hb). intros a Ha.
rewrite length_map in Ha.
apply (mbyte_of_aview SEGS).
replace a with (e_p g + (a - e_p g)) by lia.
rewrite (G3 (e_p g) (e_n g) (a - e_p g) Hin0 Hin3 ltac:(lia) ltac:(intros (r & Hr & _); destruct Hr)).
rewrite (G2 (e_p g) (e_n g) (a - e_p g) Hin0 Hin2 ltac:(lia) ltac:(intros (r & Hr & _); destruct Hr)).
reflexivity.
Qed.
(* A block allocated during the walk is not one of the entry's blocks: two copies of one block in a state's
   block list would have to be disjoint from each other. *)
Lemma p_fresh_not_old : forall ly S (W : world SEGS) mem md b m rest,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((b, m) :: rest) -> In (b, m) rest ->
  0 < req_size m -> False.
Proof.
intros ly S W mem md b m rest HAR Hperm Hin Hm.
assert (Hc : (2 <= count_occ zz_dec (ablocks B ly S) (b, m))%nat).
{ rewrite (Permutation_count_occ zz_dec) in Hperm. rewrite (Hperm (b, m)). cbn [count_occ].
  destruct (zz_dec (b, m) (b, m)) as [_ | Hne]; [|exfalso; exact (Hne eq_refl)].
  pose proof (proj1 (count_occ_In zz_dec rest (b, m)) Hin). lia. }
destruct (dup2_split (b, m) (ablocks B ly S) Hc) as (l1 & l2 & l3 & Hsplit).
pose proof (sep_blocks_pos SEGS B LAWS ly S W mem md (b, m) (b, m) l1 l2 l3 HAR Hsplit) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ---- Ph2: the NULL check, mf+144, and the payload copy ---------------------------------------------------- *)
(* What Ph2's run writes: mf+144..151 only. *)
Lemma p2_frame_keep : forall (E : env) (W : world SEGS) m m' mf,
  bv_unsigned (ew E 9) = mf -> frame_of E [p2_mf] (rd W m) (rd W m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 144 <= a < mf + 152) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros E W m m' mf U9 HF a Ha Hn. apply (aview_eq_of SEGS). apply HF.
rewrite unsigned_lit_small by exact Ha. intros (r & [<- | []] & Hr).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi p2_mf base_val] in Hr. rewrite U9 in Hr. lia.
Qed.
Lemma p2_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem mf (G : facts),
  getr regs 9 = w64 mf -> 2 ^ 46 <= mf -> mf + 320 <= 2 ^ 47 ->
  (forall a, mf + 144 <= a < mf + 152 -> apresent (w_H W) mem a) ->
  facts_ok (Eimg (Ereg regs [])) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (ss_p2 G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x4c0)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf G H9 Hlo Hhi Hpres HG.
pose proof asan_consts as (C1 & _).
assert (E9 : ew (Eimg (Ereg regs [])) 9 = w64 mf)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (U9 : base_val (Eimg (Ereg regs [])) (Some 9%nat) = mf)
  by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_p2. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, p2_mf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- exact HG.
Qed.

Theorem d1_ph2 : d1_ph2_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold d1_ph2_stmt.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3 HC HD.
destruct HD as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfrs3 & Hperm3 & Hhs3 & MLE3 & KEEP3 & HP1).
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJ2 & Hfrs2 & _ & _ & _ & HEC & Hi & _ & _ & _ & HRL).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & Hinb).
destruct HRL as (_ & _ & _ & _ & _ & Hbl2 & _ & _).
pose proof HP1 as (HRC & R10 & R22 & R27 & R26 & R18).
pose proof HRC as (Rsp & Rs1 & Rs0 & Rgp & Rtp & Rs19 & R20 & R21 & R24).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE.
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hkr : 0 <= D1k g i <= 255) by (unfold D1k; apply SlotModel.rec_k_range).
pose proof (SlotModel.rec_bounds (e_pl g) i) as (_ & Hbody0' & Hbodyk' & _ & _ & _).
assert (Hbody0 : 0 <= D1body g i) by (unfold D1body; exact Hbody0').
assert (Hbodyk : D1body g i + D1k g i <= e_n g)
  by (unfold D1body, D1k; rewrite <- Hnlen; exact Hbodyk').
assert (Hplen : length (SlotModel.rec_pl (e_pl g) i) = Z.to_nat (D1k g i))
  by (unfold D1k; apply SlotModel.rec_pl_length).
assert (Hpl : 4096 <= pl) by (inversion Hhs3 as [|hh tt Hh _]; cbn [fst] in Hh; exact Hh).
assert (Hplin : In (pl, D1k g i) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). left. reflexivity. }
assert (Hinp3 : In (e_p g, e_n g) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). right. exact Hinp2. }
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hin43 : In (4, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 pl (D1k g i) HAR3 Hplin)
  as (_ & _ & Hplce & Hplapp & _ & _ & _).
pose proof (req_size_pos0 (D1k g i) ltac:(lia)) as (Hrq0 & Hrq1).
pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrqn.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
set (E := Eimg (Ereg regs3 (@nil word))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs3 []) n)
  by (intros n Hnn; unfold E; apply Eimg_low; exact Hnn).
assert (E2 : ew E 2 = w64 mf)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact Rsp).
assert (E3 : ew E 3 = w64 (as_gp B))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 3 3%bv eq_refl); exact Rgp).
assert (E4 : ew E 4 = w64 (as_tp B))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 4 4%bv eq_refl); exact Rtp).
assert (E8 : ew E 8 = w64 (e_sp0 g))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl); exact Rs0).
assert (E9 : ew E 9 = w64 mf)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact Rs1).
assert (E10 : ew E 10 = w64 pl)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact R10).
assert (E18 : ew E 18 = w64 (e_n g - D1body g i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 (shadow_addr (SFa g pos)))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 19 19%bv eq_refl); exact Rs19).
assert (E20 : ew E 20 = w64 (Z.of_nat i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 20 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 6)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (D1k g i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 22 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = w64 (SFa g pos + V_before))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = w64 (e_p g + D1body g i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 (D1addr g i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 27 27%bv eq_refl); exact R27).
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HPR : forall a, mf + 144 <= a < mf + 152 -> apresent (w_H W3) mem3 a)
  by (intros a Ha; apply Hpres3; clear - Ha Hmfb HSTKm Has; lia).
assert (Hvm144 : forall (Wx : world SEGS) memx,
  region_ok SEGS E (rd Wx memx)
    (YP09.mkRegion (Some 9%nat) 144 152 144 152 [YP09.mkChunk 144 (CVal 8 (SOff 18 0))]) ->
  val_mem SEGS (rd Wx memx) (mf + 144) 8 (e_n g - D1body g i)).
{ intros Wx memx HR.
  apply (field_of_region E _ 9%nat mf _ 144 152 144 152 144 8 (SOff 18 0) (e_n g - D1body g i) HR U9).
  - cbn [In]. auto.
  - cbn [sv_denot]. rewrite E18, Z.add_0_r, unsigned_lit_small by lia.
    reflexivity.
  - cbn. lia.
  - cbn. lia. }
(* The numbers both cases need, proved here while the context is small. *)
assert (Hmf64 : 0 <= mf < 2 ^ 64) by (clear - Hmf0 Hmfb H47 C1 Has; lia).
assert (Hmfr1 : 2 ^ 46 <= mf) by (clear - Hmf0 C1 Has; lia).
assert (Hmfr2 : mf + 320 <= 2 ^ 47) by (clear - Hmfb H47; lia).
assert (Ho16 : (mf - e_sp0 g) mod 16 = 0).
{ clear - Hmf32 Hsp0al. apply Z.mod_divide in Hmf32; [|lia]. apply Z.mod_divide in Hsp0al; [|lia].
  apply Z.mod_divide; [lia|]. destruct Hmf32 as [q1 Eq1]. destruct Hsp0al as [q2 Eq2].
  exists (2 * q1 - q2). lia. }
assert (Hoz : mf - e_sp0 g <= 0) by (clear - Hmfb; lia).
assert (Hostk : ESTACK - (mf - e_sp0 g) <= LLVMF_STK)
  by (clear - HSTKm Has Hes HSTK; unfold STK_LLVMF in HSTK; lia).
assert (Hsp : e_sp0 g + (mf - e_sp0 g) = mf) by (clear; lia).
assert (HRET : YK0s.ret_ok (Z_to_bv 64 (BASE + 1256))) by (apply ret_ok_codeptr_v; [clear; lia | reflexivity]).
destruct (Z.eq_dec (D1k g i) 0) as [K0 | Kpos].
- (* k = 0: no copy; the record's payload is empty *)
  assert (HG : facts_ok E (mkFacts [] [] []))
    by (unfold facts_ok; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]; repeat split; exact I).
  pose proof (p2_entry W3 regs3 mem3 mf (mkFacts [] [] []) Rs1 Hmfr1 Hmfr2 HPR HG) as HS0.
  unfold ss_p2 in HS0.
  pose proof (st_ok_pi_pin_reg' E _ _ 22%bv 0 HS0
    ltac:(cbn [ms_regs restrict mkst]; rewrite R22, K0; reflexivity) eq_refl) as HS.
  clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  unfold cfg_at. change (w64 (BASE + 0x4c0)) with (Z_to_bv 64 (BASE + 0x4c0)).
  paj_run_to_shc RUNTOP HS HJ3 0x4e8.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - e_sp0 g));
    [reflexivity | rewrite U9; clear; lia | cbn [YP09.r_wlo]; clear - Hmfb HSTKm Has; lia
    | cbn [YP09.r_whi]; clear - Hmfb; lia | apply awr_ok_nil]. }
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx ?msx |- _ =>
    let r := eval vm_compute in (nth_error (ss_mem ssx) 0%nat) in
    lazymatch r with Some ?rg =>
      pose proof (st_ok_region_nth E (abs_ss VAL ssx) msx 0%nat rg HS ltac:(vm_compute; reflexivity)) as RMF
    end end.
  cbn [ms_mem restrict] in RMF.
  pose proof (Hvm144 _ _ RMF) as M144. clear RMF.
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
    prreg HS (2%bv : bv 5) Q2; prreg HS (9%bv : bv 5) Q9; prreg HS (8%bv : bv 5) Q8;
    prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (19%bv : bv 5) Q19;
    prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (24%bv : bv 5) Q24;
    prreg HS (25%bv : bv 5) Q25; prreg HS (22%bv : bv 5) Q22; prreg HS (27%bv : bv 5) Q27;
    prreg HS (26%bv : bv 5) Q26; prreg HS (18%bv : bv 5) Q18 end.
  rewrite E2 in Q2. rewrite E9 in Q9. rewrite E8 in Q8. rewrite E3 in Q3. rewrite E4 in Q4.
  rewrite E19 in Q19. rewrite E20 in Q20. rewrite E21 in Q21. rewrite E24 in Q24.
  rewrite E10 in Q25. rewrite E27 in Q27. rewrite E26 in Q26. rewrite E18 in Q18.
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- RUNS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?rF _ ?mF _) ?dF) =>
    exists ly3, S3, rF, mF, dF end.
  split; [unfold cfg_at, w64; reflexivity|].
  split; [exact HJ3|]. split; [exact Hfrs3|]. split; [exact Hperm3|]. split; [exact Hhs3|].
  split; [exact MLE3|].
  split.
  { intros a Ha Hz Hw. rewrite <- (KEEP3 a Ha Hz Hw).
    apply (p2_frame_keep E W3 mem3 _ mf U9 HFr a Ha).
    intros Hbad. apply Hw. unfold WR0. right. left. clear - Hbad. lia. }
  unfold P2.
  split; [unfold RC; repeat split; assumption|].
  split; [exact Q25|]. split; [rewrite K0; exact Q22|]. split; [exact Q27|]. split; [exact Q26|].
  split; [exact Q18|].
  split; [exact M144|].
  unfold bytes_at8.
  replace (SlotModel.rec_pl (e_pl g) i) with (@nil byte); [apply garr8_nil|].
  symmetry. apply length_zero_iff_nil. rewrite Hplen, K0. reflexivity.
- (* k > 0: the NULL check is refuted and the copy runs *)
  assert (Hk1 : 1 <= D1k g i <= 255) by (clear - Hkr Kpos; lia).
  assert (HG : facts_ok E p2_facts).
  { unfold facts_ok, p2_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|split; [|exact I]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    - rewrite E10, unsigned_lit_small by (clear - Hpl Hplce Hrq1 Hkr C1; lia).
      rewrite Z.pow_0_r, Z.mod_1_r. clear - Hpl Hplce Hrq1 Hkr C1. lia.
    - rewrite E22, unsigned_lit_small by (clear - Hkr; lia).
      rewrite Z.pow_0_r, Z.mod_1_r. clear - Hk1. lia. }
  assert (Hnotold : ~ In (pl, D1k g i) (ablocks B ly2 S2)).
  { intros Hbad. apply (p_fresh_not_old ly3 S3 W3 mem3 md3 pl (D1k g i) (ablocks B ly2 S2) HAR3 Hperm3 Hbad).
    clear - Hrq0 Hk1. lia. }
  assert (Hsep : pl + D1k g i <= e_p g + D1body g i \/ e_p g + D1body g i + D1k g i <= pl).
  { destruct (Z.le_gt_cases (pl + D1k g i) (e_p g + D1body g i)) as [Hd | Hd]; [left; exact Hd|].
    right.
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 pl (D1k g i) (e_p g) (e_n g) HAR3 Hplin Hinp3
      ltac:(intros Hbad; injection Hbad as Hbad1 Hbad2; apply Hnotold; rewrite Hbad1, Hbad2; exact Hinp2))
      as Hdis.
    unfold zdisjoint in Hdis. cbn [fst snd] in Hdis.
    clear - Hdis Hd Hbody0 Hbodyk Hrq1 Hrqn Hkr. lia. }
  assert (HbodyN : Z.of_nat (Z.to_nat (D1body g i)) = D1body g i) by (clear - Hbody0; lia).
  assert (HDST : forall a, pl <= a < pl + D1k g i ->
    awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly3 S3) ly3 [(4, pos)] a /\
    ~ (e_sp0 g + (mf - e_sp0 g) - ESTACK <= a < e_sp0 g + (mf - e_sp0 g))).
  { intros a Ha. rewrite Hsp. split.
    - right. right. left. exists pl, (D1k g i). split; [exact Hplin|]. split.
      + intros Hbad. apply Hnotold. apply (Permutation_in _ (Permutation_sym (proj1 Hbl2))). exact Hbad.
      + clear - Ha Hrq1. lia.
    - clear - Ha Hpl Hplce Hrq1 Hkr Hmf0 C1 Has Hes. lia. }
  assert (HAMD : amem_range pl (D1k g i))
    by (apply (amem_range_sub_app pl (req_size (D1k g i))); [exact Hplapp | exact Hplce | clear; lia
          | clear - Hrq1; lia | clear - Hkr; lia]).
  assert (HAMS : amem_range (e_p g + D1body g i) (D1k g i))
    by (apply (amem_range_sub_app (e_p g) (req_size (e_n g))); [exact Hpapp | exact Hpce
          | clear - Hbody0; lia | clear - Hbodyk Hrqn; lia | clear - Hkr; lia]).
  pose proof (p2_entry W3 regs3 mem3 mf p2_facts Rs1 Hmfr1 Hmfr2 HPR HG) as HS.
  change (Eimg (Ereg regs3 [])) with E in HS.
  unfold cfg_at. change (w64 (BASE + 0x4c0)) with (Z_to_bv 64 (BASE + 0x4c0)).
  paj_run_shc RUNP RUNC HS HJ3.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - e_sp0 g));
    [reflexivity | rewrite U9; clear; lia | cbn [YP09.r_wlo]; clear - Hmfb HSTKm Has; lia
    | cbn [YP09.r_whi]; clear - Hmfb; lia | apply awr_ok_nil]. }
  lazymatch goal with HS : st_ok _ _ ?ssx ?msx |- _ =>
    let r := eval vm_compute in (nth_error (ss_mem ssx) 0%nat) in
    lazymatch r with Some ?rg =>
      pose proof (st_ok_region_nth E ssx msx 0%nat rg HS ltac:(vm_compute; reflexivity)) as RMF
    end end.
  cbn [ms_mem restrict] in RMF.
  pose proof (Hvm144 _ _ RMF) as M144. clear RMF.
  lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
    prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (9%bv : bv 5) Q9;
    prreg HS (8%bv : bv 5) Q8; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
    prreg HS (19%bv : bv 5) Q19; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21;
    prreg HS (24%bv : bv 5) Q24; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
    prreg HS (12%bv : bv 5) Q12; prreg HS (25%bv : bv 5) Q25; prreg HS (22%bv : bv 5) Q22;
    prreg HS (27%bv : bv 5) Q27; prreg HS (26%bv : bv 5) Q26; prreg HS (18%bv : bv 5) Q18 end.
  rewrite E2 in Q2. rewrite E9 in Q9. rewrite E8 in Q8. rewrite E3 in Q3. rewrite E4 in Q4.
  rewrite E19 in Q19. rewrite E20 in Q20. rewrite E21 in Q21. rewrite E24 in Q24.
  rewrite E10 in Q10, Q25. rewrite E26 in Q11, Q26. rewrite E22 in Q12, Q22. rewrite E27 in Q27.
  rewrite E18 in Q18.
  assert (HSPT : forall rT : bvmap 5 word, getr rT 2 = w64 mf -> spZ rT = e_sp0 g + (mf - e_sp0 g)).
  { intros rT H2'. unfold spZ. rewrite H2', Hsp. apply unsigned_lit_small. exact Hmf64. }
  lazymatch goal with HJ3 : AJ _ _ _ _ _ ?mT ?dT _ |- _ =>
    pose proof (proj1 HJ3) as HART;
    assert (HINT : bytes_at8 W3 mT (e_p g) (e_pl g))
      by (apply (p_in_bytes g pos ly2 S2 W2 mem2 md2 ly3 S3 W3 mT dT (4 * Z.of_nat i)
                  (4 * Z.of_nat i + 1) HJ2 HJ3 Hine Hinp2 Hinp3 Hnlen (proj1 Hn) Hinb));
    assert (HPLB : bytes_at8 W3 mT (e_p g + D1body g i) (SlotModel.rec_pl (e_pl g) i))
      by (replace (e_p g + D1body g i) with (e_p g + Z.of_nat (Z.to_nat (D1body g i)))
            by (clear - Hbody0; lia);
          change (SlotModel.rec_pl (e_pl g) i)
            with (firstn (Z.to_nat (D1k g i)) (skipn (Z.to_nat (D1body g i)) (e_pl g)));
          apply (p_bytes_sub W3 mT (e_p g) (e_pl g) (Z.to_nat (D1body g i)) (Z.to_nat (D1k g i)) HINT);
          unfold SlotModel.nlen in Hnlen; clear - Hbody0 Hbodyk Hnlen Hkr; lia) end.
  pmkst HS.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
      eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA IS___asan_memcpy) AMEMCPY W3 rT mT
        LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 dT
        (4 * Z.of_nat i + 1) pl (e_p g + D1body g i) (D1k g i) (mf - e_sp0 g) _ HJ3) end.
    - exact Q10.
    - exact Q11.
    - exact Q12.
    - clear - Hkr. lia.
    - clear - Hpl. lia.
    - clear - Hpl Hplce Hrq1 Hkr C1. lia.
    - exact (HSPT _ Q2).
    - exact Ho16.
    - exact Hoz.
    - exact Hostk.
    - exact Q3.
    - exact Q4.
    - exact Q1.
    - exact HRET.
    - exact HDST.
    - exact HAMD.
    - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 _ _ pl (D1k g i) pl (D1k g i) HART Hplin);
        clear - Hrq1; lia.
    - intros Hk0.
      apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 _ _ pl (D1k g i) pl (D1k g i) HART Hplin);
        [clear; lia | clear - Hrq1; lia | exact Hk0].
    - split; [clear - Hp4096 Hbody0; lia|].
      split; [clear - Hp4096 Hpce Hcur Hbody0 Hbodyk Hrqn C1; lia|].
      split.
      { intros a Ha. split.
        - replace a with (e_p g + Z.of_nat (Z.to_nat (a - e_p g))) by (clear - Ha Hbody0; lia).
          apply (p_bytes_some W3 _ (e_p g) (e_pl g) (Z.to_nat (a - e_p g)) HINT).
          unfold SlotModel.nlen in Hnlen. clear - Ha Hbodyk Hbody0 Hnlen Hkr. lia.
        - rewrite (HSPT _ Q2), Hsp. clear - Ha Hp4096 Hpce Hmf0 C1 Has Hes Hbodyk Hbody0 Hrqn Hkr. lia. }
      split; [exact Hsep|].
      split; [exact HAMS|].
      split; [apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 _ _ (e_p g) (e_n g)
                (e_p g + D1body g i) (D1k g i) HART Hinp3); clear - Hbody0 Hbodyk Hrqn; lia|].
      intros Hk0.
      apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 _ _ (e_p g) (e_n g)
        (e_p g + D1body g i) (D1k g i) HART Hinp3);
        [clear - Hbody0; lia | clear - Hbodyk Hrqn; lia | exact Hk0]. }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha0 & Heff & Hfr4 & Hpres4).
  rewrite Hsp in Hfr4.
  apply SRr_ret.
  exists ly3, S3, regs4, mem4, md4.
  split; [unfold cfg_at, w64; reflexivity|].
  split; [exact HJ4|]. split; [exact Hfrs3|]. split; [exact Hperm3|]. split; [exact Hhs3|].
  split; [exact MLE3|].
  split.
  { intros a Ha Hz Hw. rewrite <- (KEEP3 a Ha Hz Hw).
    assert (Hout : ~ (pl <= a < pl + D1k g i)).
    { intros Hbad. apply (d1_fz_not_block B LAWS g pos ly3 S3 W3 mem3 md3 pl (D1k g i) a HAR3 Hin43 EFa3
        Hplin ltac:(clear - Hbad Hrq1; lia)).
      destruct Hz as [Hz | Hz]; [exfalso; clear - Hbad Hz Hplce Hrq1 Hkr; lia | exact Hz]. }
    rewrite (Hfr4 a Ha Hout ltac:(intros Hbad; apply Hw; unfold WR0; left; clear - Hbad Has Hes; lia)).
    apply (p2_frame_keep E W3 mem3 _ mf U9 HFr a Ha).
    intros Hbad. apply Hw. unfold WR0. right. left. clear - Hbad. lia. }
  unfold P2.
  split.
  { apply (d1_RC_pres B g pos mf i _ regs4 HP4). unfold RC. repeat split; assumption. }
  split; [rewrite (d1_presv _ regs4 25%bv HP4 ltac:(p_cs)); exact Q25|].
  split; [rewrite (d1_presv _ regs4 22%bv HP4 ltac:(p_cs)); exact Q22|].
  split; [rewrite (d1_presv _ regs4 27%bv HP4 ltac:(p_cs)); exact Q27|].
  split; [rewrite (d1_presv _ regs4 26%bv HP4 ltac:(p_cs)); exact Q26|].
  split; [rewrite (d1_presv _ regs4 18%bv HP4 ltac:(p_cs)); exact Q18|].
  split.
  { refine (val_mem_kept SEGS (w_H W3) (w_H W3) _ mem4 (mf + 144) 8 (e_n g - D1body g i) _ M144).
    intros j Hj. apply (Hfr4 (mf + 144 + j));
      [clear - Hmf64 Hmfr2 Hj; lia
      | clear - Hj Hpl Hplce Hrq1 Hkr Hmf0 C1 Has; lia
      | clear - Hj; lia]. }
  refine (p_bytes_copied W3 _ _ _ pl _ _ HPLB).
  intros j Hj. rewrite Hplen in Hj.
  rewrite (Heff j ltac:(clear - Hj Hkr; lia)). reflexivity.
Qed.

End c.
End b.
End a.
