(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its module names and addresses changed; 1329 of its 1464 lines of code are new or changed and 1008 lines of the source are left out. *)
(* The catalogue tail of segment K of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan
   0x81fa0 .. 0x82090, listing offsets 0x1894 .. 0x1984): k_cat_tail_stmt of
   lib/A/Prog/LLVMFuzzerTestOneInput_Kcut.v, from k_mid to inv_K_end.

     0x81fa0 sb zero,90(s3)     the scope byte of `count` (SF + V_cnt, one granule)
     0x81fa4 sd zero,0(s2)      count := 0
     0x81fac jal reac_box_catalogue (+0x18a0)   a0 = the catalogue, count = BOX_COUNT = 11
     0x81fb4 beqz a1            count = 11, so the count = 0 path (and its own defect call at +0x1934)
                                is not taken
     0x81fbc .. 0x81fcc         e := the catalogue + 296 * (t_row mod 11)
     0x81fe0 jal reac_box_catalogue_defect (+0x18d4)   a0 = CATALOGUE_DEFECT_MASK e in out dp I O P sP sd
     0x81fec .. 0x82050         the entry's own mask: the row's widths at e+16 and e+20 against in and out
     0x82054 .. 0x82074         e->display at e+8; when it is not null, strcmp (+0x1968) against dp
     0x82084 bne s2,s7          the two masks agree, so the abort is not taken
     0x82088 .. 0x8208c         `count` is poisoned again; 0x82090 is K's end.

   Every abort is refuted from the contract's own facts: HCAT fixes the count, HIMG's catalogue clause the
   row's fields at the call, HCATD the callee's mask and, through its post's window-keep (all bytes outside
   the callee's stack window are kept), the same row fields at the entry's own reads after the call, and
   ASTRCMP (lib/Reusable/AStrcmpDef.v, `strcmp_res c1 c2 = 0 <-> c1 = c2`) the display compare. The row is
   read-only image data (G_CAT through globs_marked), the display buffer dp a heap block of the run. The
   three paths of the entry's width compare meet at 0x82054 (kc_merge). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YN3v YI04 YI08 YI09 YI00 YI0s YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig IdentBlkTail YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_Kcut LLVMFuzzerTestOneInput_Klib.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec
reac_box_catalogue_defect_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this segment's addresses are shadow_addr and the
   catalogue row's offsets, which need it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Import RcIdentModel.

(* The callee-saved registers a call keeps, from a call's aregs_preserved and the run's kept list
   (H.v's h_pres). *)
Ltac kc_pres HKR HP :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros r Hr; rewrite <- (HKR r) by (cbn [In] in Hr |- *; tauto);
  pose proof (HP (bv_unsigned r)) as Hq; rewrite Z_to_bv_bv_unsigned in Hq; apply Hq;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- acallee_saved (bv_unsigned ?x) => let v := eval vm_compute in (bv_unsigned x) in
       change (bv_unsigned x) with v end; unfold acallee_saved; lia |]);
  destruct Hr.
(* The same, straight from a call's aregs_preserved. *)
Ltac kc_pres0 HP :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros r Hr;
  pose proof (HP (bv_unsigned r)) as Hq; rewrite Z_to_bv_bv_unsigned in Hq; apply Hq;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- acallee_saved (bv_unsigned ?x) => let v := eval vm_compute in (bv_unsigned x) in
       change (bv_unsigned x) with v end; unfold acallee_saved; lia |]);
  destruct Hr.

(* A register of a call state as the symbolic state leaves it, without normalisation (H.v's prreg_raw). *)
Ltac kc_prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

(* ---- the two masks ------------------------------------------------------------------------------------- *)
(* What the entry computes itself (the row's widths, then the display compare) is the callee's mask. *)
Lemma kc_mask_split : forall e i o d I O P (sP sd : list byte), e <> 0 -> d <> 0 ->
reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK e i o d I O P sP sd =
(if (I =? i) && (O =? o) then 0 else 1) + (if P =? 0 then 0 else if bool_decide (sP = sd) then 0 else 2).
Proof.
intros e i o d I O P sP sd He Hd.
unfold reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK.
replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; exact He).
replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd).
destruct (P =? 0); reflexivity.
Qed.

(* A list with no zero byte holds no zero byte. *)
Lemma kc_nzl_notin : forall l, nzl l -> ~ In (Z_to_bv 8 0) l.
Proof.
intros l H Hin. pose proof (proj1 (Forall_forall _ _) H _ Hin) as Hb.
unfold nzb, bz in Hb. apply Hb. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v / _Kcut.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* the registered globals of the contract (LLVMFuzzerTestOneInput.v:203) *)
Variable G : list (Z * Z).
#[local] Notation EPRE g := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS g).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)]).
(* What this segment needs, each as the contract's Section states it. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis G_CAT : In (VAL (A_OBJ 27), 3256) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  llvmf_img B G W mem.
Hypothesis HCAT : tcat_spec B (BASE + AF_reac_box_catalogue) pa_relro_lo pa_relro_hi.
Hypothesis HCATD : treac_box_catalogue_defect_spec B G.
Hypothesis ASTRCMP : AStrcmpDef.astrcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_strcmp).
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation ECOMMON := (@ecommon rc PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_K := (@inv_K_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* What a boundary of the entry's journal says of the frame, the stack and the input block (G.v G_base). *)
Lemma kc_base : forall g pos lyc Sc W mem md k hs,
  EPRE g -> AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  frame_addr lyc 4 pos = SFa g pos /\ In (4, pos) (frames Sc) /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  alloc_ceiling + LLVMF_STK <= e_sp0 g /\ e_sp0 g mod 16 = 0 /\ e_sp0 g <= 2 ^ 47 /\
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc)) /\ e_n g = Z.of_nat (length (e_pl g)) /\
  (forall a, SFa g pos <= a < SFa g pos + 1024 -> apresent (w_H W) mem a) /\
  (forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr (SFa g pos) + i)) /\
  (forall a, e_sp0 g - LLVMF_STK <= a < e_sp0 g -> apresent (w_H W) mem a).
Proof.
intros g pos lyc Sc W mem md k hs HPRE HJ Hfrs Hbl.
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr lyc 4 pos = SFa g pos)
by (unfold SFa, frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 4 pos HAR Hin) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin) as (_ & _ & HFpres & HFSpres).
rewrite EFA in HF4096, HFceil, HFapp, HF64, HFpres, HFSpres.
change (fs_frame_bytes 4) with 1024 in *. change (1024 / 8) with 128 in HFSpres.
split; [exact EFA|]. split; [exact Hin|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact HFapp|]. split; [exact HF64|].
split; [clear - Hceil Hslo; lia|]. split; [exact Hsp0al|]. split; [clear - Hshi H47; lia|].
split.
{ intros Hn. destruct Hinp as [[Hn0 _] | [_ Hine]]; [clear - Hn Hn0; lia|].
  destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
split; [exact Hlen|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [intros i Hi; exact (proj1 (HFSpres i Hi))|].
intros a Ha. apply Hpres. exact Ha.
Qed.

(* The call chain at a call the entry makes from its own frame (G.v G_chain). *)
Lemma kc_chain : forall g pos lyc Sc (W : world SEGS) memc mdc k mf,
  EPRE g -> AJ g pos lyc Sc W memc mdc k ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  val_mem SEGS (rd W memc) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memc) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  exists ch, achain lyc (aview SEGS (w_H W) memc) mf (e_sp0 g) ch.
Proof.
intros g pos lyc Sc W memc mdc k mf HPRE HJ Hmf Vra Vs0.
pose proof HPRE as (HFN & Hraz & _).
destruct HFN as (_ & _ & Hra40 & _ & _ & _ & _ & Hach & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof asan_consts as (C1 & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
change (spZ (e_regs g)) with (e_sp0 g) in Hach.
destruct (Z_lt_le_dec (e_sp0 g) (ly_top lyc - 16)) as [Hlt | Hge].
- exists [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))].
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  assert (HRAr : 0 <= RA_LLVMF < 2 ^ 64).
  { rewrite <- Hraz. unfold raZ. pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as R.
    change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  apply (achain_push lyc (aview SEGS (w_H (e_W g)) (e_mem g)) _ (e_sp0 g) (s0Z (e_regs g)) RA_LLVMF [] mf).
  + apply (achain_ly_top (e_ly g)); [exact ETop | exact Hach].
  + rewrite ETop. clear - Htop1 H47. lia.
  + intros a Ha. exact (aview_above_of_journal B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] lyc Sc W memc mdc k HJ a Ha).
  + apply rdword_of_val_mem; [exact Vra | exact HRAr].
  + apply rdword_of_val_mem; [exact Vs0 | unfold s0Z; exact Rs0r].
  + rewrite <- Hraz. exact Hra40.
  + clear - Hceil Hslo HSTK'. lia.
  + clear - Hsp0al. lia.
  + exact Hlt.
  + clear - Hmf. lia.
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* ---- the two strings of the display compare -------------------------------------------------------------- *)
(* A `bytes_at8` run is a `catd_lz` run: the byte lists the two callees name agree. *)
Lemma kc_lz : forall s : list byte, map (fun b : byte => bv_unsigned b) (s ++ [zb 0]) = catd_lz s.
Proof. intro s. unfold catd_lz. rewrite map_app. reflexivity. Qed.

(* One call of the strcmp trampoline, on the row's display string (read-only image) and the run's display
   buffer (a heap block): the result is zero exactly when the two byte lists are equal. *)
Lemma kc_strcmp_at : forall pcs g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k
  P dp capd (sP sd : list byte) retk (Q : world SEGS -> config -> Prop),
  AStrcmpDef.astrcmp_realizes SEGS B pcs ->
  AJ g pos lyc Sc W memT mdc k ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  alloc_ceiling + LLVMF_STK <= e_sp0 g -> e_sp0 g mod 16 = 0 -> e_sp0 g <= 2 ^ 47 ->
  getr regsT 10 = w64 P -> getr regsT 11 = w64 dp ->
  getr regsT 2 = w64 mf -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  catd_rostr G W memT P sP ->
  In (dp, capd) (ablocks B lyc Sc) -> bytes_at8 W memT dp (sd ++ [zb 0]) -> nzl sd ->
  Z.of_nat (length sd) + 1 <= req_size capd ->
  (forall regs3 mem3 md3 (v : word),
     AJ g pos lyc Sc W mem3 md3 k -> aregs_preserved regsT regs3 -> getr regs3 10 = v ->
     (bv_unsigned v = 0 <-> sP = sd) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
        aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem3 a) ->
     SRr SEGS W (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pcs) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros pcs g pos mf W regsT memT mdc lyc Sc k P dp capd sP sd retk Q AM HJ Hmf Hmf32 Hsp0 Hsp16 Hsp47
  R10 R11 Rsp Rgp Rtp Rra Hretk Hreven HroP Hdin Hdb Hdnz Hdcap Hk.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct HroP as (GP & NP & (qP & zP & HqP & HqP1 & HqP2) & LoP & HiP).
destruct (al_blocks _ _ LAWS lyc Sc W memT mdc dp capd HAR Hdin) as (Hd16 & Hd4096 & Hdceil & Hdapp & Hdpres & _).
assert (NDd : ~ In (Z_to_bv 8 0) sd) by (apply kc_nzl_notin; exact Hdnz).
assert (GD : garr8 SEGS (rd W memT) dp (catd_lz sd)) by (rewrite <- kc_lz; exact Hdb).
destruct (catd_k_le sP sd) as [KP KD].
destruct (catd_k_spec sP sd NP NDd) as (KS1 & KS2 & KS3).
set (kk := catd_k sP sd) in *.
assert (AVP : forall j, (j <= length sP)%nat -> aview SEGS (w_H W) memT (P + Z.of_nat j) = Some (nth j (catd_lz sP) 0))
by (intros j Hj; apply catd_garr8_aview; [exact GP | rewrite catd_lz_len; lia]).
assert (AVD : forall j, (j <= length sd)%nat -> aview SEGS (w_H W) memT (dp + Z.of_nat j) = Some (nth j (catd_lz sd) 0))
by (intros j Hj; apply catd_garr8_aview; [exact GD | rewrite catd_lz_len; lia]).
assert (Hrq : req_size capd <= capd \/ capd = 0)
by (unfold req_size; destruct (Z.eqb_spec capd 0); lia).
pose proof (req_size_pos capd ltac:(lia)) as [Hrq1 Hrq2].
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf Hsp0 Hsp47 HSTK' C1; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
assert (KPRE : forall i0, 0 <= i0 < Z.of_nat kk ->
  exists c, aview SEGS (w_H W) memT (P + i0) = Some c /\ aview SEGS (w_H W) memT (dp + i0) = Some c /\ c <> 0).
{ intros i0 Hi0. destruct (KS1 (Z.to_nat i0) ltac:(lia)) as [Eq Nz].
  exists (nth (Z.to_nat i0) (catd_lz sP) 0).
  replace (P + i0) with (P + Z.of_nat (Z.to_nat i0)) by lia.
  replace (dp + i0) with (dp + Z.of_nat (Z.to_nat i0)) by lia.
  split; [apply AVP; lia|]. split; [rewrite Eq; apply AVD; lia | exact Nz]. }
assert (KAT : exists cx cy, aview SEGS (w_H W) memT (P + Z.of_nat kk) = Some cx /\
  aview SEGS (w_H W) memT (dp + Z.of_nat kk) = Some cy /\ (cx <> cy \/ cx = 0))
by (exists (nth kk (catd_lz sP) 0), (nth kk (catd_lz sd) 0);
    split; [apply AVP; lia|]; split; [apply AVD; lia | exact KS2]).
assert (SRCP : src_ok SEGS W regsT memT P (Z.of_nat kk + 1))
by (intros a Ha; split;
    [replace a with (P + Z.of_nat (Z.to_nat (a - P))) by lia; rewrite AVP by lia; discriminate
    | rewrite Hspt, Hes; lia]).
assert (SRCD : src_ok SEGS W regsT memT dp (Z.of_nat kk + 1))
by (intros a Ha; split;
    [replace a with (dp + Z.of_nat (Z.to_nat (a - dp))) by lia; rewrite AVD by lia; discriminate
    | rewrite Hspt, Hes; lia]).
destruct (ro_read_ok_glob SEGS B G lyc Sc W memT mdc qP zP P (Z.of_nat kk + 1) GM HqP IV HAR
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [RAP HULLP].
pose proof (range_addressable_of_block SEGS B LAWS lyc Sc W memT mdc dp capd dp (Z.of_nat kk + 1) HAR Hdin
  ltac:(lia) ltac:(lia)) as RAD.
pose proof (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W memT mdc dp capd dp (Z.of_nat kk + 1) HAR Hdin
  ltac:(lia) ltac:(lia) ltac:(lia)) as HULLD.
pose proof (amem_range_of_block SEGS B LAWS lyc Sc W memT mdc dp capd dp (Z.of_nat kk + 1) HAR Hdin
  ltac:(lia) ltac:(lia)) as AMD.
assert (AMP : amem_range P (Z.of_nat kk + 1)) by (unfold amem_range; left; rewrite C5; lia).
eapply SRr_bind.
{ eapply (aj_strcmp_at B LAWS pcs AM W regsT memT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g)
    (e_md g) [(4, pos)] lyc Sc mdc k P dp (Z.of_nat kk) (mf - e_sp0 g) (Z_to_bv 64 (BASE + retk)));
  [ exact HJ | exact R10 | exact R11 | lia | lia | lia | lia | lia | lia
  | rewrite Hspt; ring
  | pose proof (Z.div_mod mf 32 ltac:(lia)) as D1; pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2;
    rewrite Hmf32, Z.add_0_r in D1; rewrite Hsp16, Z.add_0_r in D2;
    replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia);
    apply Z_mod_mult
  | clear - Hmf; lia
  | rewrite Hes; clear - Hmf HSTK'; lia
  | exact Rgp | exact Rtp | exact Rra | apply ret_ok_codeptr_v; [exact Hretk | exact Hreven]
  | exact KPRE | exact KAT | exact SRCP | exact SRCD
  | intros a Ha; replace (e_sp0 g + (mf - e_sp0 g)) with mf by ring; rewrite Hes;
    clear - Ha kk LoP HiP KP Hmf Hsp0 HSTK' C1 C2 C3 C4 C5; lia
  | intros a Ha; replace (e_sp0 g + (mf - e_sp0 g)) with mf by ring; rewrite Hes;
    clear - Ha kk Hd4096 Hdceil Hmf Hsp0 HSTK' C1 C2 C3 C4 C5 KD Hdcap Hrq1 Hrq2; lia
  | exact AMP | exact AMD | exact RAP | exact HULLP | exact RAD | exact HULLD ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpres2).
replace (e_sp0 g + (mf - e_sp0 g)) with mf in Hfr by ring.
assert (CMP : bv_unsigned v = 0 <-> sP = sd).
{ rewrite <- KS3. rewrite (AVP kk ltac:(lia)), (AVD kk ltac:(lia)) in Hcmp. split.
  - intros H0. assert (Hv0 : v = w64 0) by (apply bv_eq; rewrite H0; reflexivity).
    apply Hcmp in Hv0. injection Hv0 as Hv0. exact Hv0.
  - intros H0. assert (Hv0 : v = w64 0) by (apply Hcmp; rewrite H0; reflexivity).
    rewrite Hv0. reflexivity. }
apply (Hk regs2 mem2 md2 v HJ2 HP2 Hv CMP); [|exact Hpres2].
intros a Ha Hna. apply (Hfr a Ha). rewrite Hes in Hna |- *. exact Hna.
Qed.

(* ---- what a call of this segment keeps ---------------------------------------------------------------------- *)
(* the entry's frame and its shadow, the input block, the run's three output buffers, and the machine stack
   from mf up: every address the boundary and the walk speak of *)
Definition kfz (g : ectx) (pos a : Z) : Prop :=
  (SFa g pos <= a < SFa g pos + 1024) \/ (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128).
Definition kinb (g : ectx) (a : Z) : Prop := 0 < e_n g /\ e_p g <= a < e_p g + e_n g.
Definition koutb (g : ectx) (nm tk dp a : Z) : Prop :=
  exists b n j, In (b, n) (k_blocks g nm tk dp) /\ 0 <= j < req_size n /\ a = b + j.
Definition kprot (g : ectx) (pos mf nm tk dp a : Z) : Prop :=
  (mf <= a < e_sp0 g) \/ kfz g pos a \/ kinb g a \/ koutb g nm tk dp a.

(* The three kept-clauses every call post states, in the shape the boundary needs (G.v gkept_of). *)
Lemma kc_kept_of : forall g pos mf nm tk dp lyc Sc (W : world SEGS) memc mem3 (E WR : Z -> Prop) slo,
  frame_addr lyc 4 pos = SFa g pos -> In (4, pos) (frames Sc) ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc)) ->
  (forall b n, In (b, n) (k_blocks g nm tk dp) -> In (b, n) (ablocks B lyc Sc)) ->
  alloc_ceiling <= mf -> e_sp0 g <= 2 ^ 47 ->
  (forall a, E a -> WR a) -> (forall a, slo <= a < mf -> WR a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < mf) -> ~ E a ->
     aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a) ->
  (forall b n i, In (b, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> ~ E (b + i) ->
     aview SEGS (w_H W) mem3 (b + i) = aview SEGS (w_H W) memc (b + i)) ->
  (forall cid ps a, In (cid, ps) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, ps)) \/
      in_zr a (shadow_addr (frame_addr lyc cid ps), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a) ->
  forall a, kprot g pos mf nm tk dp a -> ~ WR a ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a.
Proof.
intros g pos mf nm tk dp lyc Sc W memc mem3 E WR slo EFA Hin4 Hinp Hbls Hce Hsp47 HEW HSW K1 K2 K4 a Ha Hw.
assert (HnE : ~ E a) by (intros HEa; exact (Hw (HEW a HEa))).
destruct Ha as [Ha | [Ha | [Ha | (b & n & j & Hbn & Hj & ->)]]].
- apply K1; [lia | intros Hs; exact (Hw (HSW a Hs)) | exact HnE].
- apply (K4 4 pos a Hin4); [|exact HnE].
  unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4) with 1024.
  change (1024 / 8) with 128. unfold kfz in Ha. destruct Ha; [left | right]; lia.
- destruct Ha as (Hn & Ha1 & Ha2). replace a with (e_p g + (a - e_p g)) by lia.
  apply (K2 _ _ _ (Hinp Hn)); [pose proof (req_size_pos (e_n g) ltac:(lia)); lia|].
  replace (e_p g + (a - e_p g)) with a by lia. exact HnE.
- apply (K2 b n j (Hbls b n Hbn) Hj). exact HnE.
Qed.

(* A value the symbolic state holds in a region chunk is in memory (H.v h_val_of_st_ok). *)
Lemma kc_val_of_st_ok : forall E ss ms r nb off (sz : N) e v,
  st_ok SEGS E ss ms -> In r (ss_mem ss) -> YP09.r_base r = Some nb ->
  In (YP09.mkChunk off (CVal sz e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N sz) -> Z.of_N sz <= 8 ->
  val_mem SEGS (ms_mem ms) (bv_unsigned (ew E nb) + off) (N.to_nat sz) v.
Proof.
intros E ss ms r nb off sz e v HS Hin Hb Hc He Hv Hsz.
pose proof (st_ok_mem_ok SEGS E _ ms HS) as HM.
pose proof (mem_ok_region SEGS E (ms_mem ms) _ r HM Hin) as (_ & _ & _ & Hcs).
rewrite Hb in Hcs. cbn [base_val] in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
exact (val_of_chunk_ok SEGS E (ms_mem ms) _ off sz e v Hck He Hv Hsz).
Qed.

(* bytes of a side-stack frame the callee may write (H.v h_twr_frame) *)
Lemma kc_twr_frame : forall STK sp0 FP ly S W0 mem md lyc Sc W memc mdc k sp pos q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem md [(4, pos)] lyc Sc W memc mdc k ->
  frame_addr lyc 4 pos <= q -> q + n <= frame_addr lyc 4 pos + 1024 -> alloc_ceiling <= sp - ESTACK ->
  twr_ok B STK sp0 FP ly S lyc Sc [(4, pos)] W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem md lyc Sc W memc mdc k sp pos q n HJ H1 H2 Hsp a Ha.
assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc [(4, pos)] a).
{ right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  change (fs_frame_bytes 4) with 1024. lia. }
destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
pose proof HJ as (HAR & _). pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR) as Fb.
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|].
pose proof asan_consts as (C1 & _).
assert (Hin : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
destruct (Fb Hin) as (_ & F1 & _). change (fs_frame_bytes 4) with 1024 in F1. lia.
Qed.

(* ---- K's end ------------------------------------------------------------------------------------------------ *)
(* inv_K_end at 0x82090 from k_mid's state: the journal at the final memory, the callee-saved registers the
   boundary names, and every byte the boundary speaks of kept but `count` and its scope byte (Klib's k_rne). *)
Lemma kc_finish : forall g pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regsF memF mdF,
  AJ g pos ly2 S2 W2 memF mdF (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  hblocks B g ly2 S2 (k_blocks g nm tk dp) ->
  getr regs2 21 = w64 tk -> getr regs2 22 = w64 dp ->
  val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 21; 22]%bv -> getr regsF r = getr regs2 r) ->
  (forall a, kprot g pos mf nm tk dp a -> ~ (SFa g pos + V_cnt <= a < SFa g pos + V_cnt + 8) ->
     ~ (shadow_addr (SFa g pos) + 90 <= a < shadow_addr (SFa g pos) + 91) ->
     aview SEGS (w_H W2) memF a = aview SEGS (w_H W2) mem2 a) ->
  INV_K g pos mf nm tk dp W2 (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 0x1984)) memF (seg_rom SEGS)) mdF).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsF memF mdF HJ Hfrs Hk MLE MOK HC Hbl R21 R22 V184 RS KP.
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
destruct (kc_base g pos ly2 S2 W2 memF mdF _ _ HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinp & Hlen & _ & _ & _).
pose proof HJ as (HAR & _).
assert (Hsh1 : shadow_addr (SFa g pos) + 128 <= alloc_ceiling)
by (pose proof HSFapp as Hap; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap;
    unfold shadow_addr, SHADOW_OFF; lia).
assert (HshSF : shadow_addr (SFa g pos) + 128 <= SFa g pos \/ SFa g pos + 1024 <= shadow_addr (SFa g pos))
by (pose proof HSFapp as Hap; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap;
    unfold shadow_addr, SHADOW_OFF; lia).
assert (VK : forall a (n : nat) v,
  (forall kk, 0 <= kk < Z.of_nat n -> kprot g pos mf nm tk dp (a + kk) /\
     ~ (SFa g pos + V_cnt <= a + kk < SFa g pos + V_cnt + 8) /\
     ~ (shadow_addr (SFa g pos) + 90 <= a + kk < shadow_addr (SFa g pos) + 91)) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 memF) a n v).
{ intros a n v Hns Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk.
  destruct (Hns kk Hkk) as (X1 & X2 & X3). exact (KP _ X1 X2 X3). }
assert (VS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= e_sp0 g ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 memF) a n v).
{ intros a n v H0 H1 Hv. apply VK; [|exact Hv]. intros kk Hkk.
  split; [unfold kprot; left; lia|]. unfold V_cnt. split; lia. }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
assert (HINP : forall kk, 0 <= kk < Z.of_nat (length (map (fun b : byte => bv_unsigned b) (e_pl g))) ->
  aview SEGS (w_H W2) memF (e_p g + kk) = aview SEGS (w_H W2) mem2 (e_p g + kk)).
{ intros kk Hkk. rewrite length_map, <- Hlen in Hkk.
  assert (Hn : 0 < e_n g) by lia.
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  apply KP.
  - unfold kprot, kinb. right; right; left. split; [exact Hn | lia].
  - intros X. apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 memF mdF (e_p g) (e_n g) kk 4 pos HAR (Hinp Hn) Hin4);
    [lia|]. left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4) with 1024.
    unfold V_cnt in X. lia.
  - intros X. apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 memF mdF (e_p g) (e_n g) kk 4 pos HAR (Hinp Hn) Hin4);
    [lia|]. right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4 / 8) with 128. lia. }
unfold inv_K_end, acut. exists ly2, S2, regsF, memF, mdF.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon.
  rewrite !(RS 2%bv), !(RS 9%bv), !(RS 8%bv), !(RS 3%bv), !(RS 4%bv), !(RS 19%bv) by (cbn; tauto).
  refine (conj Rsp (conj Rs1 (conj Rs0 (conj Hmfb (conj Hmf32 (conj Rgp (conj Rtp (conj Rs3 _)))))))).
  repeat match goal with
  | |- _ /\ _ => split
  | |- e_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HPRE
  | |- forall fd, _ => intros fd; rewrite Efd; reflexivity
  | |- m_fs _ = m_fs (e_md g) => exact Efs
  | |- bytes_at8 _ _ (e_p g) _ => unfold bytes_at8 in *; apply (k_garr8_moved W2 mem2 memF _ _ HINP Hinb)
  | |- val_mem _ _ (SFa g pos + 1016) _ _ => apply VK; [|exact Vflag];
       intros kk Hkk; split; [unfold kprot, kfz; right; left; left; lia | unfold V_cnt; split; lia]
  | |- val_mem _ _ ?a _ _ => apply VS; [lia | lia | assumption]
  end. }
split; [exact Hbl|]. split; [rewrite (RS 22%bv) by (cbn; tauto); exact R22|].
split; [rewrite (RS 21%bv) by (cbn; tauto); exact R21|].
apply VS; [lia | lia | exact V184].
Qed.

(* ---- the symbolic states of the straight-line runs --------------------------------------------------------- *)
(* the shadow byte of `count` (x19 = shadow_addr SF, offset 90) and the word `count` itself (x18 = SF + V_cnt) *)
Definition kc_shr : YP09.region := YP09.mkRegion (Some 19%nat) 90 91 90 91 [].
Definition kc_cnr : YP09.region := YP09.mkRegion (Some 18%nat) 0 8 0 8 [].
Definition kc_ss1 : sstate := mkSS 0x1894 sr_atoms [kc_shr; kc_cnr] None (mkFacts [] [] []).
(* 0x81fb0 .. 0x81fe0: the count (x18, now 11) and the row index at mf + 136 (x9) *)
Definition kc_cntr : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 11))].
Definition kc_rowr : YP09.region :=
  YP09.mkRegion (Some 9%nat) 136 144 136 136 [YP09.mkChunk 136 (CVal 8 (SOff 32 0))].
Definition kc_ss2 : sstate := mkSS 0x18a4 sr_atoms [kc_cntr; kc_rowr] None (mkFacts [] [] []).
(* 0x81fc0 .. 0x81fcc: e = the catalogue (x10) + 296 * (row mod 11), as the engine leaves it in x10 / x20 *)
Lemma kc_e_denot : forall E c r,
  ew E 10 = Z_to_bv 64 c -> ew E 32 = Z_to_bv 64 r -> 0 <= c < 2 ^ 48 -> 0 <= r < 256 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SMd M_REMU (SOff 32 0) (SLit 11)) (SLit 296)))
    (SLit 0)) = c + 296 * (r mod 11) /\
  U E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SMd M_REMU (SOff 32 0) (SLit 11)) (SLit 296))) =
    c + 296 * (r mod 11).
Proof.
intros E c r H10 H32 Hc Hr.
pose proof (Z.mod_pos_bound r 11 ltac:(lia)) as Hm.
assert (HI : U E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SMd M_REMU (SOff 32 0) (SLit 11)) (SLit 296))) =
  c + 296 * (r mod 11)).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SMd. cbn [zmd_raw]. rewrite !U_SLit.
  rewrite (U_atom E 10 c H10) by lia. rewrite (U_atom E 32 r H32) by lia.
  rewrite (zcanon_id 11) by (unfold M64; lia). rewrite (zcanon_id 296) by (unfold M64; lia).
  cbn [Z.eqb Pos.eqb].
  rewrite (zcanon_id (r mod 11)) by (unfold M64; lia).
  rewrite (zcanon_id (r mod 11 * 296)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia. }
split; [|exact HI].
rewrite U_SAlu. cbn [zalu_raw]. rewrite HI, U_SLit. rewrite (zcanon_id 0) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the compares of the entry's own mask, as arithmetic ---------------------------------------------------- *)
Lemma kc_br_ne32 : forall E n m x y, ew E n = Z_to_bv 64 (x mod 2 ^ 32) -> -2 ^ 31 <= x < 2 ^ 31 ->
  bv_unsigned (ew E m) = y -> 0 <= y < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SOff m 0)) = negb (x =? y).
Proof.
intros E n m x y Hn Hx Hm Hy. rewrite branch_ne_U. f_equal.
rewrite (catd_sext E n x Hn Hx), U_SOff, Hm, Z.add_0_r. unfold zcanon, M64.
replace (x mod 2 ^ 64 =? y mod 2 ^ 64) with (x mod 2 ^ 64 =? y mod 2 ^ 64 mod 2 ^ 64)
  by (rewrite Z.mod_mod by lia; reflexivity).
rewrite Z.mod_mod by lia. apply catd_eqb32; lia.
Qed.
Lemma kc_br_eqz : forall E n v, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v H Hv. rewrite branch_eq_U, U_SOff, U_SLit, H, Z.add_0_r. unfold zcanon, M64.
rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma kc_br_nel : forall E n v s, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 -> 0 <= s < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit s)) = negb (v =? s).
Proof.
intros E n v s H Hv Hs. rewrite branch_ne_U, U_SOff, U_SLit, H, Z.add_0_r. unfold zcanon, M64.
rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma kc_br_ne_rr : forall E n m x y, bv_unsigned (ew E n) = x -> bv_unsigned (ew E m) = y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = negb (x =? y).
Proof.
intros E n m x y Hx Hy Rx Ry. rewrite branch_ne_U, !U_SOff, Hx, Hy, !Z.add_0_r. unfold zcanon, M64.
rewrite !Z.mod_small by lia. reflexivity.
Qed.
(* 0x82078 .. 0x82080: s7 |= (strcmp != 0) << 1 *)
Lemma kc_or_fin : forall E s vu, (s = 0 \/ s = 1) -> 0 <= vu < 2 ^ 64 ->
  bv_unsigned (ew E 23) = s -> bv_unsigned (ew E 10) = vu ->
  U E (SAlu ALU_OR (SOff 23 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 10 0)) (SLit 1))) =
  s + (if vu =? 0 then 0 else 2).
Proof.
intros E s vu Hs Hv H23 H10.
rewrite !U_SAlu, !U_SLit, !U_SOff, H23, H10, !Z.add_0_r. cbn [zalu_raw].
rewrite (zcanon_id vu) by (unfold M64; lia).
destruct (Z.eqb_spec vu 0) as [->|NZ].
- destruct Hs as [-> | ->]; vm_compute; reflexivity.
- replace (zcanon 0 <? vu) with true
    by (symmetry; apply Z.ltb_lt; unfold zcanon, M64; rewrite Z.mod_0_l by lia; lia).
  destruct Hs as [-> | ->]; vm_compute; reflexivity.
Qed.
Lemma kc_br_ne_or : forall E m s vu, (s = 0 \/ s = 1) -> 0 <= vu < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  bv_unsigned (ew E 23) = s -> bv_unsigned (ew E 10) = vu -> bv_unsigned (ew E 18) = m ->
  branch_taken BC_NE (sv_denot E (SOff 18 0))
    (sv_denot E (SAlu ALU_OR (SOff 23 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 10 0)) (SLit 1)))) =
  negb (m =? s + (if vu =? 0 then 0 else 2)).
Proof.
intros E m s vu Hs Hv Hm H23 H10 H18. rewrite branch_ne_U, (kc_or_fin E s vu Hs Hv H23 H10), U_SOff, H18,
  Z.add_0_r. unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* What the runs of the tail and the strcmp call keep: every byte but `count`'s scope byte and the callee's
   stack window below mf. *)
Definition kc_kept_m (s lo hi : Z) (W : world SEGS) (m m0 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (s <= a < s + 1) -> ~ (lo <= a < hi) ->
  aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.
Ltac kc_win U19 :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Eq := fresh "Eq" in
  intros bb wlo whi aa Hin Hr; unfold windows in Hin; cbn in Hin;
  repeat (destruct Hin as [Eq | Hin];
    [injection Eq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U19 in Hr; lia] |]);
  destruct Hin.
Ltac kc_upd U19 KM :=
  lazymatch goal with
  | HFr : frame_of ?E ?ssm (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    lazymatch type of KM with kc_kept_m ?s ?lo ?hi ?W _ ?m0 =>
      let KM' := fresh "KM" in
      assert (KM' : kc_kept_m s lo hi W m2 m0);
      [ let a := fresh "a" in let Ha := fresh "Ha" in let H1 := fresh "H1" in let H2 := fresh "H2" in
        intros a Ha H1 H2; transitivity (aview SEGS (w_H W) m1 a); [|exact (KM a Ha H1 H2)];
        apply (kept_of_frame E ssm H m1 m2 (fun x => s <= x < s + 1) HFr); [kc_win U19 | exact Ha | exact H1]
      | clear KM; rename KM' into KM ]
    end
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* 0x81fe4 .. 0x82090: the row on x20 = e (P atom 34, I atom 35, O atom 36, each as stored), the row's shadow
   cells on atom 33 = shadow_addr e (e is 8-aligned: e+8 is cell 1, e+16 and e+20 cell 2), the shadow base at
   mf + 176 (atom 32), and the scope byte of `count` on x19, written at 0x8208c. *)
Definition kc_er : YP09.region := YP09.mkRegion (Some 20%nat) 8 24 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 4 (SOff 35 0));
   YP09.mkChunk 20 (CVal 4 (SOff 36 0))].
Definition kc_esh : YP09.region := YP09.mkRegion (Some 33%nat) 1 3 0 0
  [YP09.mkChunk 1 (CVal 1 (SLit 0)); YP09.mkChunk 2 (CVal 1 (SLit 0))].
Definition kc_mfsb : YP09.region :=
  YP09.mkRegion (Some 9%nat) 176 184 176 176 [YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
Definition kc_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 16) (SLit 3)) (SOff 32 0), SOff 33 2);
   (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 20) (SLit 3)) (SOff 32 0), SOff 33 2);
   (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 8) (SLit 3)) (SOff 32 0), SOff 33 1)].
Definition kc_ss3 : sstate :=
  mkSS 0x18d8 sr_atoms [kc_er; kc_esh; kc_mfsb; kc_shr] None (mkFacts [] [] kc_alias).
(* 0x82078 .. 0x82090, after the strcmp of the display: only `count`'s scope byte is touched *)
Definition kc_ss4 : sstate := mkSS 0x196c sr_atoms [kc_shr] None (mkFacts [] [] []).
(* 0x82054 .. 0x82090, from the merge of the three paths of the entry's own width compare (s7 = 0 or 1):
   the row's display pointer on x20 = e (atom 33 = P), its shadow cell on atom 32 = shadow_addr e (a3 = x13 holds
   the shadow base), and the scope byte of `count` on x19 *)
Definition kc_mer : YP09.region :=
  YP09.mkRegion (Some 20%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition kc_msh : YP09.region := YP09.mkRegion (Some 32%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SLit 0))].
Definition kc_ss5 : sstate :=
  mkSS 0x1948 sr_atoms [kc_mer; kc_msh; kc_shr] None
    (mkFacts [] [] [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 8) (SLit 3)) (SOff 13 0), SOff 32 1)]).
Definition kc_x3 (she P I O : Z) : list word :=
  map (Z_to_bv 64) [SHADOW_OFF; she; P; I mod 2 ^ 32; O mod 2 ^ 32].
Ltac kc_awr U19 EFA pos :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros a (r & Hr & Ha); cbn [ss_mem In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ try (unfold kc_er, kc_esh, kc_mfsb, kc_shr, kc_mer, kc_msh in Ha);
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite U19 in Ha; right; right; right; exists 4, pos; split; [left; reflexivity|];
              right; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 4 / 8) with 128; lia ]
    |]);
  destruct Hr.
Lemma kc_garr8_km : forall s lo hi (W : world SEGS) m m0 a l,
  kc_kept_m s lo hi W m m0 ->
  (forall k, 0 <= k < Z.of_nat (length l) -> 0 <= a + k < 2 ^ 64 /\ ~ (s <= a + k < s + 1) /\
     ~ (lo <= a + k < hi)) ->
  garr8 SEGS (rd W m0) a l -> garr8 SEGS (rd W m) a l.
Proof.
intros s lo hi W m m0 a l KM Hk Hg. apply (k_garr8_moved W m0 m a l); [|exact Hg].
intros k Hk'. destruct (Hk k Hk') as (X1 & X2 & X3). exact (KM (a + k) X1 X2 X3).
Qed.
Lemma kc_vm1 : forall H mem a v, aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv j Hj. assert (j = 0%nat) by lia. subst j. rewrite Z.add_0_r.
destruct (aview_byte SEGS H mem a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned b) 256 Hr). reflexivity.
Qed.

(* 0x82054 .. 0x82090: the display compare and the mask check, from the merge of the entry's width-compare
   paths with s7 = s; x18 holds the callee's mask, which the caller has split as s + the display part. *)
Lemma kc_merge : forall g pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regsM memM mdM mem4
  ee s P (sP : list byte),
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  hblocks B g ly2 S2 (k_blocks g nm tk dp) -> SlotModel.n_r (e_pl g) = 0 ->
  getr regs2 21 = w64 tk -> getr regs2 22 = w64 dp ->
  val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm ->
  AJ g pos ly2 S2 W2 memM mdM (4 * Z.of_nat (m_nrec g) + 7) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 21; 22]%bv -> getr regsM r = getr regs2 r) ->
  getr regsM 20 = w64 ee -> getr regsM 13 = w64 SHADOW_OFF -> getr regsM 23 = w64 s -> (s = 0 \/ s = 1) ->
  getr regsM 18 = w64 (s + (if P =? 0 then 0 else if bool_decide (sP = SlotModel.n_EXP_DP (e_pl g)) then 0 else 2)) ->
  kc_kept_m (shadow_addr (SFa g pos) + 90) (mf - 8192) mf W2 memM mem4 ->
  (forall a, kprot g pos mf nm tk dp a -> ~ (SFa g pos + V_cnt <= a < SFa g pos + V_cnt + 8) ->
     ~ (shadow_addr (SFa g pos) + 90 <= a < shadow_addr (SFa g pos) + 91) ->
     aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a) ->
  bytes_at8 W2 mem4 dp (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0]) ->
  ee mod 8 = 0 -> IMG_LO <= ee + 8 -> ee + 24 <= IMG_TOP -> 0 <= P < 2 ^ 64 ->
  val_mem SEGS (rd W2 mem4) (ee + 8) 8 P ->
  aview SEGS (w_H W2) mem4 (SHADOW_OFF + ee / 8 + 1) = Some 0 ->
  (P <> 0 -> catd_rostr G W2 mem4 P sP) ->
  SRr SEGS W2 (mkCfg (mkst regsM (Z_to_bv 64 (BASE + 0x1948)) memM (seg_rom SEGS)) mdM)
    (INV_K g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsM memM mdM mem4 ee s P sP
  Hfrs Hk MLE MOK HC Hbl Hr0 R21 R22 V184 HJ RS R20 R13 R23 Hs R18 KM KP Hdpb Hee8 Hlo Hhi HPr VP SH1 HroP.
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO.
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
destruct (kc_base g pos ly2 S2 W2 memM mdM _ _ HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinp & Hlen & HFpres & HFSpres & Hstkpres).
pose proof HJ as (HAR & _).
pose proof (frm_off_imgP B ly2 S2 W2 memM mdM 4 pos HAR Hin4) as Hoff.
rewrite EFA in Hoff. change (fs_frame_bytes 4) with 1024 in Hoff.
assert (Hshv : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (HshSF : shadow_addr (SFa g pos) + 128 <= SFa g pos \/ SFa g pos + 1024 <= shadow_addr (SFa g pos))
by (pose proof HSFapp as Hap; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap;
    rewrite Hshv; unfold SHADOW_OFF; lia).
assert (Hsh1 : 2147450880 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling)
by (pose proof HSFapp as Hap; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap;
    rewrite Hshv; unfold SHADOW_OFF; lia).
assert (Hmm : 0 <= (s + (if P =? 0 then 0 else if bool_decide (sP = SlotModel.n_EXP_DP (e_pl g)) then 0 else 2)) <= 3)
  by (destruct Hs as [-> | ->]; destruct (P =? 0);
      [| destruct (bool_decide (sP = SlotModel.n_EXP_DP (e_pl g))) | | destruct (bool_decide (sP = SlotModel.n_EXP_DP (e_pl g)))];
      lia).
assert (Hmm2 : 0 <= (s + (if P =? 0 then 0 else if bool_decide (sP = SlotModel.n_EXP_DP (e_pl g)) then 0 else 2)) < 2 ^ 64) by lia.
(* the row's display pointer and its shadow cell are where the caller read them *)
assert (VPm : val_mem SEGS (rd W2 memM) (ee + 8) 8 P).
{ eapply (val_mem_kept SEGS); [|exact VP]. intros kk Hkk.
  apply KM; rewrite ?Hshv; unfold SHADOW_OFF; lia. }
assert (SH1m : aview SEGS (w_H W2) memM (SHADOW_OFF + ee / 8 + 1) = Some 0).
{ rewrite (KM (SHADOW_OFF + ee / 8 + 1)); [exact SH1 | | |]; rewrite ?Hshv; unfold SHADOW_OFF; lia. }
remember (Eimg (Ereg regsM [Z_to_bv 64 (SHADOW_OFF + ee / 8); Z_to_bv 64 P])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (ER2 : regs_ok E2 sr_atoms regsM) by (rewrite HE2; apply regs_ok_Eimg_Ereg).
assert (AGE2 : env_agree 32 (Ereg regsM [Z_to_bv 64 (SHADOW_OFF + ee / 8); Z_to_bv 64 P]) E2)
  by (rewrite HE2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regsM r)
  by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EL2 : forall n, (n < A_TEXT)%nat ->
  ew E2 n = ew (Ereg regsM [Z_to_bv 64 (SHADOW_OFF + ee / 8); Z_to_bv 64 P]) n)
  by (intros n Hn; rewrite HE2; apply Eimg_low; exact Hn).
assert (E32 : ew E2 32 = Z_to_bv 64 (SHADOW_OFF + ee / 8))
  by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 0)).
assert (E33 : ew E2 33 = Z_to_bv 64 P)
  by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsM _ 1)).
assert (EB : ew E2 A_TEXT = Z_to_bv 64 BASE)
  by (rewrite HE2; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
clear HE2.
assert (U19 : bv_unsigned (ew E2 19) = shadow_addr (SFa g pos))
  by (rewrite (EE2 19%nat 19%bv eq_refl), (RS 19%bv ltac:(cbn; tauto)), Rs3; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E2 20) = ee)
  by (rewrite (EE2 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E2 13) = SHADOW_OFF)
  by (rewrite (EE2 13%nat 13%bv eq_refl), R13; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U18 : bv_unsigned (ew E2 18) = (s + (if P =? 0 then 0 else if bool_decide (sP = SlotModel.n_EXP_DP (e_pl g)) then 0 else 2)))
  by (rewrite (EE2 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E2 23) = s)
  by (rewrite (EE2 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; destruct Hs; lia).
assert (U32 : bv_unsigned (ew E2 32) = SHADOW_OFF + ee / 8)
  by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E2 33) = P) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E2 kc_ss5
  (restrict (w_H W2) (mkst regsM (Z_to_bv 64 (BASE + 0x1948)) memM (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kc_ss5. apply pa_entry_st_ok_full.
  - exact ER2.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold kc_mer, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E2 _ ee 8 8 (SOff 33 0) P);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact VPm].
    + unfold kc_msh, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E2 _ (SHADOW_OFF + ee / 8) 1 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply kc_vm1. exact SH1m.
    + unfold kc_shr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (shadow_addr (SFa g pos) + o) with (shadow_addr (SFa g pos) + 90) by lia.
      exact (HFSpres 90 ltac:(lia)).
  - apply pairwise_disjoint_of_extents.
    unfold kc_mer, kc_msh, kc_shr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U20, U32, U19. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite Hshv in *. unfold SHADOW_OFF in *. repeat split; try exact Logic.I; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat match goal with |- _ /\ _ => split | |- True => exact Logic.I end;
    apply U_inj; rewrite U_SAlu, U_srl3, !U_SOff, U20, U13, U32; cbn [zalu_raw]; unfold zcanon, M64;
    rewrite !Z.mod_small by (unfold SHADOW_OFF; lia); unfold SHADOW_OFF; lia. }
assert (KPROT : forall a, kprot g pos mf nm tk dp a -> 0 <= a < 2 ^ 64 /\ ~ (mf - 8192 <= a < mf)).
{ destruct Hbl as (Hperm & _).
  intros a [Ha | [Ha | [Ha | (b & n & j & Hbn & Hj & ->)]]].
  - lia.
  - unfold kfz in Ha. destruct Ha; lia.
  - destruct Ha as (Hn & Ha1 & Ha2).
    destruct (al_blocks _ _ LAWS ly2 S2 W2 memM mdM _ _ HAR (Hinp Hn)) as (_ & Hb1 & Hb2 & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)). lia.
  - assert (Hin : In (b, n) (ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hbn).
    destruct (al_blocks _ _ LAWS ly2 S2 W2 memM mdM _ _ HAR Hin) as (_ & Hb1 & Hb2 & _). lia. }
(* the display buffer: n_EXP_DP and a NUL, no zero byte inside, room for both in dp *)
destruct (k_r0 (e_pl g) Hr0) as [Hwok Hfits].
destruct (k_fits (e_pl g) Hfits) as (_ & _ & Hld). unfold SlotModel.n_ld in Hld.
pose proof (k_exp_dp_nz (e_pl g) Hwok) as Hdnz.
assert (Hdin : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly2 S2)).
{ destruct Hbl as (Hperm & _).
  apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; right; right; left; reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 memM mdM _ _ HAR Hdin) as (_ & Hdlo & Hdbd & _).
pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(lia)) as [Hrq1 Hrq2].
assert (Hdcap : Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1 <=
  req_size (Z.max (SlotModel.t_cap_disp (e_pl g)) 1)) by lia.
paj_run_shc RUNP RUNC HS HJ.
{ kc_awr U19 EFA pos. }
kc_upd U19 KM.
(* 0x8206c: the row's display pointer *)
psrr_branch_pi RUNP BR HS.
- rewrite (kc_br_eqz E2 33 P U33 HPr) in Hc. apply Z.eqb_eq in Hc. rename Hc into HP0.
  paj_run_shc RUNP RUNC HS HJ.
  { kc_awr U19 EFA pos. }
  kc_upd U19 KM.
  (* 0x82084: the two masks agree *)
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite (kc_br_ne_rr E2 18 23 _ s U18 U23 ltac:(lia) ltac:(destruct Hs; lia)) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc. apply Hc. rewrite HP0. cbn [Z.eqb]. lia.
  + clear Hc. paj_run_to_shc RUNTOP HS HJ 0x1984.
    { kc_awr U19 EFA pos. }
    kc_upd U19 KM.
    apply SRr_ret. pmkst HS.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msF) |- _ =>
      pose proof (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W2) msF) regsM _
        [2; 3; 4; 8; 9; 19; 21; 22]%bv HS AGE2 ltac:(vm_compute; reflexivity)) as HKF;
      cbn [ms_regs restrict] in HKF;
      eapply (kc_finish g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs msF) (ms_mem msF) _ HJ Hfrs Hk
        MLE MOK HC Hbl R21 R22 V184);
      [ intros r Hr; rewrite (HKF r Hr); apply RS; cbn [In] in Hr |- *; tauto
      | intros a Ha H1 H2; destruct (KPROT a Ha) as [Ha0 Ha1];
        rewrite (KM a Ha0 ltac:(intros X; apply H2; lia) Ha1); exact (KP a Ha H1 H2) ]
    end.
- rewrite (kc_br_eqz E2 33 P U33 HPr) in Hc. apply Z.eqb_neq in Hc. rename Hc into HPn.
  paj_run_shc RUNP RUNC HS HJ.
  { kc_awr U19 EFA pos. }
  kc_upd U19 KM.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msc) |- _ =>
    prreg HS (1%bv : bv 5) Qc1; prreg HS (10%bv : bv 5) Qc10; prreg HS (11%bv : bv 5) Qc11;
    pose proof (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W2) msc) regsM _
      [2; 3; 4; 8; 9; 18; 19; 21; 22; 23]%bv HS AGE2 ltac:(vm_compute; reflexivity)) as HKc;
    cbn [ms_regs restrict] in HKc;
    pmkst HS; rename msc into msC
  end.
  destruct (HroP HPn) as (GP & NP & GLP & LoP & HiP).
  apply (kc_strcmp_at _ g pos mf W2 (ms_regs msC) (ms_mem msC) _ ly2 S2 _ P dp
    (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) sP (SlotModel.n_EXP_DP (e_pl g)) 6508 _ ASTRCMP HJ
    Hmfb Hmf32 Hsp0 Hsp16 Hsp47).
  + rewrite Qc10, E33. reflexivity.
  + rewrite Qc11, (EE2 22%nat 22%bv eq_refl), (RS 22%bv ltac:(cbn; tauto)). exact R22.
  + rewrite (HKc 2%bv ltac:(cbn; tauto)), (RS 2%bv ltac:(cbn; tauto)). exact Rsp.
  + rewrite (HKc 3%bv ltac:(cbn; tauto)), (RS 3%bv ltac:(cbn; tauto)). exact Rgp.
  + rewrite (HKc 4%bv ltac:(cbn; tauto)), (RS 4%bv ltac:(cbn; tauto)). exact Rtp.
  + exact Qc1.
  + lia.
  + reflexivity.
  + split; [|split; [exact NP | split; [exact GLP | split; [exact LoP | exact HiP]]]].
    apply (kc_garr8_km _ _ _ W2 (ms_mem msC) mem4 P _ KM); [|exact GP].
    intros k0 Hk0. rewrite catd_lz_len in Hk0. lia.
  + exact Hdin.
  + unfold bytes_at8 in *. apply (kc_garr8_km _ _ _ W2 (ms_mem msC) mem4 dp _ KM); [|exact Hdpb].
    intros k0 Hk0. rewrite length_map, length_app in Hk0. cbn [length] in Hk0.
    split; [lia|]. split; [|lia].
    intros X. apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 _ _ dp _ k0 4 pos HAR Hdin Hin4); [lia|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4 / 8) with 128. lia.
  + exact Hdnz.
  + exact Hdcap.
  + intros regs3 mem3 md3 v HJ3' HP3' Hv CMP KS3 PS3.
    (* what the call kept, and the callee-saved registers *)
    assert (KM3 : kc_kept_m (shadow_addr (SFa g pos) + 90) (mf - 8192) mf W2 mem3 mem4).
    { intros a Ha H1 H2. rewrite (KS3 a Ha ltac:(unfold ESTACK; lia)). exact (KM a Ha H1 H2). }
    clear KM KS3. rename KM3 into KM.
    assert (P3c : forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23]%bv ->
      getr regs3 r = getr (ms_regs msC) r) by (kc_pres0 HP3').
    destruct (kc_base g pos ly2 S2 W2 mem3 md3 _ _ HPRE HJ3' Hfrs Hbl) as (_ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & HFSpres3 & _).
    remember (Eimg (Ereg regs3 [])) as E3 eqn:HE3.
    assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply Eimg_env).
    assert (ER3 : regs_ok E3 sr_atoms regs3) by (rewrite HE3; apply regs_ok_Eimg_Ereg).
    assert (AGE3 : env_agree 32 (Ereg regs3 []) E3)
      by (rewrite HE3; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
      by (intros n r Hn; rewrite HE3; apply ew_Eimg_Ereg_nat; exact Hn).
    clear HE3.
    assert (U19c : bv_unsigned (ew E3 19) = shadow_addr (SFa g pos))
      by (rewrite (EE3 19%nat 19%bv eq_refl), (P3c 19%bv ltac:(cbn; tauto)), (HKc 19%bv ltac:(cbn; tauto)),
          (RS 19%bv ltac:(cbn; tauto)), Rs3; apply unsigned_lit_small; lia).
    assert (HS3 : st_ok_pi SEGS VAL E3 kc_ss4
      (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + 0x196c)) mem3 (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. unfold kc_ss4. apply pa_entry_st_ok_full.
      - exact ER3.
      - vm_compute. reflexivity.
      - constructor; [|constructor].
        unfold kc_shr, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U19c. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS).
        replace (shadow_addr (SFa g pos) + o) with (shadow_addr (SFa g pos) + 90) by lia.
        exact (HFSpres3 90 ltac:(lia)).
      - cbn [pairwise_disjoint all_disjoint]. split; exact Logic.I.
      - split; [exact Logic.I | split; [exact Logic.I | exact Logic.I]]. }
    paj_run_shc RUNP RUNC HS3 HJ3'.
    { kc_awr U19c EFA pos. }
    kc_upd U19c KM.
    assert (U18c : bv_unsigned (ew E3 18) = (s + (if P =? 0 then 0 else if bool_decide (sP = SlotModel.n_EXP_DP (e_pl g)) then 0 else 2)))
      by (rewrite (EE3 18%nat 18%bv eq_refl), (P3c 18%bv ltac:(cbn; tauto)), (HKc 18%bv ltac:(cbn; tauto)), R18;
          apply unsigned_lit_small; lia).
    assert (U23c : bv_unsigned (ew E3 23) = s)
      by (rewrite (EE3 23%nat 23%bv eq_refl), (P3c 23%bv ltac:(cbn; tauto)), (HKc 23%bv ltac:(cbn; tauto)), R23;
          apply unsigned_lit_small; destruct Hs; lia).
    assert (U10c : bv_unsigned (ew E3 10) = bv_unsigned v)
      by (rewrite (EE3 10%nat 10%bv eq_refl), Hv; reflexivity).
    pose proof (bv_unsigned_in_range 64 v) as Rv. change (bv_modulus 64) with (2 ^ 64) in Rv.
    (* 0x82084: the two masks agree *)
    psrr_branch_pi RUNP BR HS3.
    { exfalso.
      rewrite (kc_br_ne_or E3 _ s (bv_unsigned v) Hs Rv Hmm2 U23c U10c U18c) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
      replace (P =? 0) with false by (symmetry; apply Z.eqb_neq; exact HPn).
      destruct (Z.eqb_spec (bv_unsigned v) 0) as [V0 | V0].
      - rewrite (catd_bd_true _ _ (proj1 CMP V0)). reflexivity.
      - rewrite (catd_bd_false _ _ (fun Q => V0 (proj2 CMP Q))). reflexivity. }
    clear Hc. paj_run_to_shc RUNTOP HS3 HJ3' 0x1984.
    { kc_awr U19c EFA pos. }
    kc_upd U19c KM.
    apply SRr_ret. pmkst HS3.
    lazymatch goal with HS3 : st_ok_pi _ _ _ _ (restrict _ ?msF) |- _ =>
      pose proof (regs_kept_of_st_ok SEGS E3 _ (restrict (w_H W2) msF) regs3 []
        [2; 3; 4; 8; 9; 19; 21; 22]%bv HS3 AGE3 ltac:(vm_compute; reflexivity)) as HKF;
      cbn [ms_regs restrict] in HKF;
      eapply (kc_finish g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs msF) (ms_mem msF) _ HJ3' Hfrs Hk
        MLE MOK HC Hbl R21 R22 V184);
      [ intros r Hr; rewrite (HKF r Hr), (P3c r ltac:(revert Hr; cbn [In]; tauto)),
          (HKc r ltac:(revert Hr; cbn [In]; tauto)); apply RS; revert Hr; cbn [In]; tauto
      | intros a Ha H1 H2; destruct (KPROT a Ha) as [Ha0 Ha1];
        rewrite (KM a Ha0 ltac:(intros X; apply H2; lia) Ha1); exact (KP a Ha H1 H2) ]
    end.
Qed.

(* 0x81fe4 .. 0x82090, from the return of reac_box_catalogue_defect: the entry's own mask and the end of K.
   The row's fields at the post-call memory are premises: they are what the caller states of the row. *)
Lemma kc_tail : forall g pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs4 mem4 md4
  ee rr (I O P : Z) (sP : list byte),
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  hblocks B g ly2 S2 (k_blocks g nm tk dp) -> SlotModel.n_r (e_pl g) = 0 ->
  getr regs2 21 = w64 tk -> getr regs2 22 = w64 dp ->
  getr regs2 24 = w64 (SlotModel.t_in (e_pl g)) -> getr regs2 25 = w64 (SlotModel.t_out (e_pl g)) ->
  val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm ->
  AJ g pos ly2 S2 W2 mem4 md4 (4 * Z.of_nat (m_nrec g) + 7) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 21; 22; 24; 25]%bv -> getr regs4 r = getr regs2 r) ->
  getr regs4 20 = w64 ee -> getr regs4 23 = w64 (VAL (A_OBJ 27)) ->
  getr regs4 10 = w64 (reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK ee (SlotModel.t_in (e_pl g))
    (SlotModel.t_out (e_pl g)) dp I O P sP (SlotModel.n_EXP_DP (e_pl g))) ->
  (forall a, kprot g pos mf nm tk dp a -> ~ (SFa g pos + V_cnt <= a < SFa g pos + V_cnt + 8) ->
     ~ (shadow_addr (SFa g pos) + 90 <= a < shadow_addr (SFa g pos) + 91) ->
     aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a) ->
  bytes_at8 W2 mem4 dp (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0]) ->
  ee = VAL (A_OBJ 27) + 296 * rr -> 0 <= rr < 11 -> VAL (A_OBJ 27) mod 8 = 0 ->
  IMG_LO <= ee + 8 -> ee + 24 <= IMG_TOP ->
  -2 ^ 31 <= I < 2 ^ 31 -> -2 ^ 31 <= O < 2 ^ 31 -> 0 <= P < 2 ^ 64 ->
  val_mem SEGS (rd W2 mem4) (ee + 8) 8 P -> val_mem SEGS (rd W2 mem4) (ee + 16) 4 I ->
  val_mem SEGS (rd W2 mem4) (ee + 20) 4 O ->
  (P <> 0 -> catd_rostr G W2 mem4 P sP) ->
  SRr SEGS W2 (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + 0x18d8)) mem4 (seg_rom SEGS)) md4)
    (INV_K g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 ee rr I O P sP
  Hfrs Hk MLE MOK HC Hbl Hr0 R21 R22 R24 R25 V184 HJ RS R20 R23 R10 KP Hdpb Eee Hrr Hcat8 Hlo Hhi
  HIr HOr HPr VP VI VO HroP.
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO.
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
destruct (kc_base g pos ly2 S2 W2 mem4 md4 _ _ HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinp & Hlen & HFpres & HFSpres & Hstkpres).
pose proof HJ as (HAR & _).
pose proof (pa_obj_img 27 ltac:(lia)) as Hcatb.
pose proof (frm_off_imgP B ly2 S2 W2 mem4 md4 4 pos HAR Hin4) as Hoff.
rewrite EFA in Hoff. change (fs_frame_bytes 4) with 1024 in Hoff.
assert (Hshv : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (HshSF : shadow_addr (SFa g pos) + 128 <= SFa g pos \/ SFa g pos + 1024 <= shadow_addr (SFa g pos))
by (pose proof HSFapp as Hap; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap;
    rewrite Hshv; unfold SHADOW_OFF; lia).
assert (Hsh1 : 2147450880 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling)
by (pose proof HSFapp as Hap; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap;
    rewrite Hshv; unfold SHADOW_OFF; lia).
assert (Hee8 : ee mod 8 = 0) by (rewrite Eee; lia).
(* the row's two shadow cells are zero: the catalogue is a registered global of 407 whole granules *)
destruct (GM ly2 S2 W2 mem4 md4 (VAL (A_OBJ 27)) 3256 G_CAT HAR) as (_ & _ & Hbs).
assert (SHC : forall c, 1 <= c <= 2 ->
  aview SEGS (w_H W2) mem4 (SHADOW_OFF + ee / 8 + c) = Some 0).
{ intros c Hc. pose proof (Hbs (37 * rr + c) ltac:(lia)) as Hb. unfold shadow_of_addr in Hb.
  replace (SHADOW_OFF + VAL (A_OBJ 27) / 8 + (37 * rr + c)) with (SHADOW_OFF + ee / 8 + c) in Hb
    by (rewrite Eee; lia).
  rewrite Hb. replace (37 * rr + c <? 3256 / 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
(* the machine-frame word mf + 176 is where it was *)
assert (V176' : val_mem SEGS (rd W2 mem4) (mf + 176) 8 SHADOW_OFF).
{ eapply (val_mem_kept SEGS); [|exact V176]. intros kk Hkk.
  apply KP; [unfold kprot; left; lia | unfold V_cnt; lia | lia]. }
remember (Eimg (Ereg regs4 (kc_x3 (SHADOW_OFF + ee / 8) P I O))) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (ER2 : regs_ok E2 sr_atoms regs4) by (rewrite HE2; apply regs_ok_Eimg_Ereg).
assert (AGE2 : env_agree 32 (Ereg regs4 (kc_x3 (SHADOW_OFF + ee / 8) P I O)) E2)
  by (rewrite HE2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs4 r)
  by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EL2 : forall n, (n < A_TEXT)%nat -> ew E2 n = ew (Ereg regs4 (kc_x3 (SHADOW_OFF + ee / 8) P I O)) n)
  by (intros n Hn; rewrite HE2; apply Eimg_low; exact Hn).
assert (E32 : ew E2 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
assert (E33 : ew E2 33 = Z_to_bv 64 (SHADOW_OFF + ee / 8))
  by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 1)).
assert (E34 : ew E2 34 = Z_to_bv 64 P)
  by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 2)).
assert (E35 : ew E2 35 = Z_to_bv 64 (I mod 2 ^ 32))
  by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 3)).
assert (E36 : ew E2 36 = Z_to_bv 64 (O mod 2 ^ 32))
  by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 4)).
assert (EB : ew E2 A_TEXT = Z_to_bv 64 BASE)
  by (rewrite HE2; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
clear HE2.
assert (U9 : bv_unsigned (ew E2 9) = mf)
  by (rewrite (EE2 9%nat 9%bv eq_refl), (RS 9%bv ltac:(cbn; tauto)), Rs1; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E2 19) = shadow_addr (SFa g pos))
  by (rewrite (EE2 19%nat 19%bv eq_refl), (RS 19%bv ltac:(cbn; tauto)), Rs3; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E2 20) = ee)
  by (rewrite (EE2 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E2 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E2 33) = SHADOW_OFF + ee / 8)
  by (rewrite E33; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi SEGS VAL E2 kc_ss3
  (restrict (w_H W2) (mkst regs4 (Z_to_bv 64 (BASE + 0x18d8)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kc_ss3. apply pa_entry_st_ok_full.
  - exact ER2.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + unfold kc_er, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E2 _ ee 8 8 (SOff 34 0) P);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact VP].
      * apply (chunk_ok_val SEGS E2 _ ee 16 4 (SOff 35 0) (I mod 2 ^ 32));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        exact (catd_val_mem_mod _ _ 4 I VI).
      * apply (chunk_ok_val SEGS E2 _ ee 20 4 (SOff 36 0) (O mod 2 ^ 32));
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        exact (catd_val_mem_mod _ _ 4 O VO).
    + unfold kc_esh, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E2 _ (SHADOW_OFF + ee / 8) 1 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        apply kc_vm1. exact (SHC 1 ltac:(lia)).
      * apply (chunk_ok_val SEGS E2 _ (SHADOW_OFF + ee / 8) 2 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        apply kc_vm1. exact (SHC 2 ltac:(lia)).
    + unfold kc_mfsb, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E2 _ mf 176 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; unfold SHADOW_OFF; lia
      | cbn; lia | exact V176'].
    + unfold kc_shr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (shadow_addr (SFa g pos) + o) with (shadow_addr (SFa g pos) + 90) by lia.
      exact (HFSpres 90 ltac:(lia)).
  - apply pairwise_disjoint_of_extents.
    unfold kc_er, kc_esh, kc_mfsb, kc_shr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U20, U33, U9, U19. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite Hshv in *. unfold SHADOW_OFF in *. repeat split; try exact Logic.I; lia.
  - unfold facts_ok, kc_alias. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat match goal with |- _ /\ _ => split | |- True => exact Logic.I end;
    apply U_inj; rewrite U_SAlu, U_srl3, !U_SOff, U20, U32, U33; cbn [zalu_raw]; unfold zcanon, M64;
    rewrite !Z.mod_small by (unfold SHADOW_OFF; lia); unfold SHADOW_OFF; lia. }
assert (KM : kc_kept_m (shadow_addr (SFa g pos) + 90) (mf - 8192) mf W2 mem4 mem4)
  by (intros a _ _ _; reflexivity).
paj_run_shc RUNP RUNC HS HJ.
{ kc_awr U19 EFA pos. }
kc_upd U19 KM.
assert (Htin : 0 <= SlotModel.t_in (e_pl g) < 256)
  by (pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 1)); unfold SlotModel.t_in, SlotModel.tb; lia).
assert (Htout : 0 <= SlotModel.t_out (e_pl g) < 256)
  by (pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 2)); unfold SlotModel.t_out, SlotModel.tb; lia).
assert (U23 : bv_unsigned (ew E2 23) = VAL (A_OBJ 27))
  by (rewrite (EE2 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E2 24) = SlotModel.t_in (e_pl g))
  by (rewrite (EE2 24%nat 24%bv eq_refl), (RS 24%bv ltac:(cbn; tauto)), R24; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E2 25) = SlotModel.t_out (e_pl g))
  by (rewrite (EE2 25%nat 25%bv eq_refl), (RS 25%bv ltac:(cbn; tauto)), R25; apply unsigned_lit_small; lia).
(* the mask the callee returned, split as the entry computes it *)
assert (Hdp : 4096 <= dp).
{ destruct Hbl as (Hperm & _).
  assert (Hin : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; right; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem4 md4 _ _ HAR Hin) as (_ & Hb & _). exact Hb. }
assert (HMs : reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK ee (SlotModel.t_in (e_pl g))
    (SlotModel.t_out (e_pl g)) dp I O P sP (SlotModel.n_EXP_DP (e_pl g)) =
  (if (I =? SlotModel.t_in (e_pl g)) && (O =? SlotModel.t_out (e_pl g)) then 0 else 1) +
  (if P =? 0 then 0 else if bool_decide (sP = SlotModel.n_EXP_DP (e_pl g)) then 0 else 2))
  by (apply kc_mask_split; lia).
(* 0x81fe8: s7 holds the catalogue, which is not 0 *)
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
  rewrite U_SOff, U_SLit, U23 in Hc. unfold zcanon, M64 in Hc. rewrite !Z.mod_small in Hc by lia. lia. }
clear Hc. paj_run_shc RUNP RUNC HS HJ.
{ kc_awr U19 EFA pos. }
kc_upd U19 KM.
(* 0x82008: the row's input width against the input's; a mismatch goes to 0x82050 (s7 = 1) *)
psrr_branch_pi RUNP BR HS.
- rewrite (kc_br_ne32 E2 35 24 I _ E35 HIr U24 ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hs7 : (if (I =? SlotModel.t_in (e_pl g)) && (O =? SlotModel.t_out (e_pl g)) then 0 else 1) = 1)
    by (replace (I =? SlotModel.t_in (e_pl g)) with false by (symmetry; apply Z.eqb_neq; exact Hc); reflexivity).
  clear Hc.
  paj_run_to_shc RUNTOP HS HJ 0x1948.
  { kc_awr U19 EFA pos. }
  kc_upd U19 KM.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msM) |- _ =>
    prreg HS (13%bv : bv 5) Qm13; prreg HS (18%bv : bv 5) Qm18; prreg HS (23%bv : bv 5) Qm23;
    pose proof (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W2) msM) regs4 _
      [2; 3; 4; 8; 9; 19; 20; 21; 22]%bv HS AGE2 ltac:(vm_compute; reflexivity)) as HKm;
    cbn [ms_regs restrict] in HKm; pmkst HS; rename msM into msK
  end.
  apply (kc_merge g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs msK) (ms_mem msK) _ mem4 ee 1 P sP
    Hfrs Hk MLE MOK HC Hbl Hr0 R21 R22 V184 HJ);
  [ intros r Hr; rewrite (HKm r ltac:(revert Hr; cbn [In]; tauto)); apply RS; revert Hr; cbn [In]; tauto
  | rewrite (HKm 20%bv ltac:(cbn; tauto)); exact R20
  | rewrite Qm13, E32; reflexivity
  | rewrite Qm23; reflexivity
  | right; reflexivity
  | rewrite Qm18, (EE2 10%nat 10%bv eq_refl), R10, HMs, Hs7; reflexivity
  | exact KM | exact KP | exact Hdpb | exact Hee8 | exact Hlo | exact Hhi | exact HPr | exact VP
  | exact (SHC 1 ltac:(lia)) | exact HroP ].
- rewrite (kc_br_ne32 E2 35 24 I _ E35 HIr U24 ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  rename Hc into HIeq.
  paj_run_shc RUNP RUNC HS HJ.
  { kc_awr U19 EFA pos. }
  kc_upd U19 KM.
  (* 0x82024: the row's output width against the output's; a match sets s7 = 0 *)
  psrr_branch_pi RUNP BR HS.
  + rewrite (kc_br_ne32 E2 36 25 O _ E36 HOr U25 ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    assert (Hs7 : (if (I =? SlotModel.t_in (e_pl g)) && (O =? SlotModel.t_out (e_pl g)) then 0 else 1) = 1)
      by (replace (O =? SlotModel.t_out (e_pl g)) with false by (symmetry; apply Z.eqb_neq; exact Hc);
          rewrite andb_false_r; reflexivity).
    clear Hc.
    paj_run_to_shc RUNTOP HS HJ 0x1948.
    { kc_awr U19 EFA pos. }
    kc_upd U19 KM.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msM) |- _ =>
      prreg HS (13%bv : bv 5) Qm13; prreg HS (18%bv : bv 5) Qm18; prreg HS (23%bv : bv 5) Qm23;
      pose proof (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W2) msM) regs4 _
        [2; 3; 4; 8; 9; 19; 20; 21; 22]%bv HS AGE2 ltac:(vm_compute; reflexivity)) as HKm;
      cbn [ms_regs restrict] in HKm; pmkst HS; rename msM into msK
    end.
    apply (kc_merge g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs msK) (ms_mem msK) _ mem4 ee 1 P sP
      Hfrs Hk MLE MOK HC Hbl Hr0 R21 R22 V184 HJ);
    [ intros r Hr; rewrite (HKm r ltac:(revert Hr; cbn [In]; tauto)); apply RS; revert Hr; cbn [In]; tauto
    | rewrite (HKm 20%bv ltac:(cbn; tauto)); exact R20
    | rewrite Qm13, E32; reflexivity
    | rewrite Qm23; reflexivity
    | right; reflexivity
    | rewrite Qm18, (EE2 10%nat 10%bv eq_refl), R10, HMs, Hs7; reflexivity
    | exact KM | exact KP | exact Hdpb | exact Hee8 | exact Hlo | exact Hhi | exact HPr | exact VP
    | exact (SHC 1 ltac:(lia)) | exact HroP ].
  + rewrite (kc_br_ne32 E2 36 25 O _ E36 HOr U25 ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hs7 : (if (I =? SlotModel.t_in (e_pl g)) && (O =? SlotModel.t_out (e_pl g)) then 0 else 1) = 0)
      by (rewrite HIeq, Hc, !Z.eqb_refl; reflexivity).
    clear Hc.
    paj_run_to_shc RUNTOP HS HJ 0x1948.
    { kc_awr U19 EFA pos. }
    kc_upd U19 KM.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msM) |- _ =>
      prreg HS (13%bv : bv 5) Qm13; prreg HS (18%bv : bv 5) Qm18; prreg HS (23%bv : bv 5) Qm23;
      pose proof (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W2) msM) regs4 _
        [2; 3; 4; 8; 9; 19; 20; 21; 22]%bv HS AGE2 ltac:(vm_compute; reflexivity)) as HKm;
      cbn [ms_regs restrict] in HKm; pmkst HS; rename msM into msK
    end.
    apply (kc_merge g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs msK) (ms_mem msK) _ mem4 ee 0 P sP
      Hfrs Hk MLE MOK HC Hbl Hr0 R21 R22 V184 HJ);
    [ intros r Hr; rewrite (HKm r ltac:(revert Hr; cbn [In]; tauto)); apply RS; revert Hr; cbn [In]; tauto
    | rewrite (HKm 20%bv ltac:(cbn; tauto)); exact R20
    | rewrite Qm13, E32; reflexivity
    | rewrite Qm23; reflexivity
    | left; reflexivity
    | rewrite Qm18, (EE2 10%nat 10%bv eq_refl), R10, HMs, Hs7; reflexivity
    | exact KM | exact KP | exact Hdpb | exact Hee8 | exact Hlo | exact Hhi | exact HPr | exact VP
    | exact (SHC 1 ltac:(lia)) | exact HroP ].
Qed.

Theorem k_cat_tail : k_cat_tail_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf nm tk dp W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HPb).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HPb as (Hbl & Hr0 & R18 & R21 & R22 & R24 & R25 & V136 & V184 & Hdpb).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (kc_base g pos ly2 S2 W2 mem2 md2 _ _ HPRE HJ Hfrs Hbl)
  as (EFA & Hin4 & HSF0 & HSF1 & HSFapp & HSF64 & Hsp0 & Hsp16 & Hsp47 & Hinp & Hlen & HFpres & HFSpres & Hstkpres).
set (SF := SFa g pos) in *. set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (HshSF : sh + 128 <= SF \/ SF + 1024 <= sh).
{ pose proof HSFapp as Hap. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap.
  pose proof Esh as Esh'. unfold SHADOW_OFF in Esh'. lia. }
assert (Hsh1 : 2147450880 <= sh /\ sh + 128 <= alloc_ceiling)
by (pose proof Esh as Esh2; unfold SHADOW_OFF in Esh2; lia).
assert (Hmfr : 0 <= mf < 2 ^ 64) by lia.
assert (Hshcnt : shadow_addr (SF + V_cnt) = sh + 90)
by (unfold shadow_addr, V_cnt; lia).
remember (Eimg (Ereg regs2 [])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (ER0 : regs_ok E0 sr_atoms regs2) by (rewrite HE0; apply regs_ok_Eimg_Ereg).
assert (AGE0 : env_agree 32 (Ereg regs2 []) E0)
  by (rewrite HE0; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs2 r)
  by (intros n r Hn; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E0 19) = sh)
by (rewrite (EE0 19%nat 19%bv eq_refl), Rs3; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E0 18) = SF + V_cnt)
by (rewrite (EE0 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; unfold V_cnt; lia).
assert (EB : ew E0 A_TEXT = Z_to_bv 64 BASE)
by (rewrite HE0; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
clear HE0.
assert (HS : st_ok_pi SEGS VAL E0 kc_ss1
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1894)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kc_ss1. apply pa_entry_st_ok_full.
  - exact ER0.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold kc_shr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (sh + o) with (sh + 90) by lia. exact (HFSpres 90 ltac:(lia)).
    + unfold kc_cnr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U18. split; [unfold V_cnt; lia|].
      split; [unfold V_cnt; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HFpres. unfold V_cnt. lia.
  - apply pairwise_disjoint_of_extents.
    unfold kc_shr, kc_cnr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U19, U18. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold V_cnt. repeat split; try exact I; lia.
  - split; [exact I | split; [exact I | exact I]]. }
unfold cfg_at. change (w64 (BASE + 0x1894)) with (Z_to_bv 64 (BASE + 0x1894)).
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold kc_shr, kc_cnr in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - rewrite U19 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA.
    change (fs_frame_bytes 4 / 8) with 128. lia.
  - rewrite U18 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA.
    change (fs_frame_bytes 4) with 1024. unfold V_cnt in Ha. lia. }
(* the shadow byte of `count` is zero, which is what reac_box_catalogue asks of its argument *)
assert (VSH : aview SEGS (w_H W2) (ms_mem ms) (sh + 90) = Some 0).
{ pose proof (kc_val_of_st_ok E0 _ _
    (YP09.mkRegion (Some 19%nat) 90 91 90 91 [YP09.mkChunk 90 (CVal 1 (SLit 0))])
    19%nat 90 1%N (SLit 0) 0 HS ltac:(cbn [ss_mem setpc In]; left; reflexivity) eq_refl
    ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite U19 in V. cbn [ms_mem restrict] in V.
  apply (aview_of_val_mem1 SEGS (w_H W2) (ms_mem ms)) in V; [exact V | lia]. }
(* the two stores are the only bytes the run changed *)
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 90 <= a < sh + 91) ->
  ~ (SF + V_cnt <= a < SF + V_cnt + 8) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame E0 _ (w_H W2) mem2 (ms_mem ms)
    (fun x => (sh + 90 <= x < sh + 91) \/ (SF + V_cnt <= x < SF + V_cnt + 8)) HFr);
  [| exact Ha | intros [H | H]; [exact (H1 H) | exact (H2 H)]].
  intros bb wlo whi aa Hin Hr. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [rewrite U19 in Hr; left; lia | rewrite U18 in Hr; right; lia]. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
pose proof (regs_kept_of_st_ok SEGS E0 _ (restrict (w_H W2) ms) regs2 []
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS AGE0 ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
assert (Usp : spZ (ms_regs ms) = mf)
by (unfold spZ; rewrite (HKR 2%bv ltac:(cbn; tauto)), Rsp; unfold w64; apply unsigned_lit_small; lia).
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & _ & Hnev0 & _ & HROS & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
assert (Haro : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) (ms_mem ms))).
{ apply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
    (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 (ms_mem ms) _ _ HJ). apply HRO. exact HROS. }
pmkst HS. rewrite (PSIG IS_reac_box_catalogue AF_reac_box_catalogue eq_refl).
eapply SRr_bind.
{ apply (HCAT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2
    (ms_mem ms) _ _ (ms_regs ms) (SF + V_cnt) HJ).
  - exact Haro.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite (HKR 3%bv ltac:(cbn; tauto)). exact Rgp.
  - rewrite (HKR 4%bv ltac:(cbn; tauto)). exact Rtp.
  - rewrite Q10, (EE0 18%nat 18%bv eq_refl). exact R18.
  - rewrite Usp. lia.
  - rewrite Usp. unfold CAT_STK, ESTACK. lia.
  - rewrite Usp. lia.
  - unfold V_cnt. lia.
  - rewrite Usp. right. unfold CAT_STK, ESTACK, V_cnt. lia.
  - rewrite Usp. eapply kc_twr_frame;
      [exact HJ | rewrite EFA; unfold V_cnt; lia | rewrite EFA; unfold V_cnt; lia | rewrite Hes; lia].
  - left. exists 4, pos. split; [exact Hin4|]. split.
    + intros a Ha. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA.
      change (fs_frame_bytes 4) with 1024. unfold V_cnt in *. lia.
    + rewrite Hshcnt. exact VSH.
  - unfold EV_CAT. lia. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & R10c & Vcnt & HK3).
rewrite Q1. unfold EV_CAT in HJ3. rewrite Z.add_0_r in HJ3.
(* what the catalogue call kept: everything the boundary speaks of, but the count word *)
pose proof Hbl as (Hperm & _).
assert (HBin : forall b n, In (b, n) (k_blocks g nm tk dp) -> In (b, n) (ablocks B ly2 S2))
by (intros b n Hin; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hin).
assert (HBbd : forall b n, In (b, n) (k_blocks g nm tk dp) -> 4096 <= b /\ b + req_size n <= alloc_ceiling).
{ intros b n Hin. destruct (al_blocks _ _ LAWS ly2 S2 W2 _ _ b n HAR (HBin b n Hin))
    as (_ & Hb1 & Hb2 & _). split; [exact Hb1 | exact Hb2]. }
assert (HIbd : 0 < e_n g -> 4096 <= e_p g /\ e_p g + req_size (e_n g) <= alloc_ceiling).
{ intros Hn. destruct (al_blocks _ _ LAWS ly2 S2 W2 _ _ (e_p g) (e_n g) HAR (Hinp Hn))
    as (_ & Hb1 & Hb2 & _). split; [exact Hb1 | exact Hb2]. }
assert (PBELOW : forall a, kprot g pos mf nm tk dp a -> mf <= a < e_sp0 g \/ 0 <= a < alloc_ceiling).
{ intros a [Ha | [Ha | [Ha | (b & n & j & Hbn & Hj & ->)]]].
  - left. exact Ha.
  - right. unfold kfz in Ha. fold SF in Ha. fold sh in Ha. destruct Ha; lia.
  - right. destruct Ha as (Hn & Ha1 & Ha2). destruct (HIbd Hn).
    pose proof (req_size_pos (e_n g) ltac:(lia)). lia.
  - right. destruct (HBbd b n Hbn). lia. }
assert (KEEP1 : forall a, kprot g pos mf nm tk dp a -> ~ (SF + V_cnt <= a < SF + V_cnt + 8) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) (ms_mem ms) a).
{ intros a Ha Hn. destruct HK3 as (K1 & K2 & _ & K4 & _).
  apply (kc_kept_of g pos mf nm tk dp ly2 S2 W2 (ms_mem ms) mem3
    (fun x => SF + V_cnt <= x < SF + V_cnt + 8)
    (fun x => (SF + V_cnt <= x < SF + V_cnt + 8) \/ (mf - CAT_STK <= x < mf)) (mf - CAT_STK)
    EFA Hin4 Hinp HBin ltac:(lia) Hsp47 ltac:(intros x Hx; left; exact Hx)
    ltac:(intros x Hx; right; exact Hx));
  [ intros x Hx1 Hx2 Hx3; rewrite Usp in K1; exact (K1 x Hx1 Hx2 Hx3)
  | intros b n i Hb Hi HE; exact (K2 b n i Hb Hi HE)
  | intros cid ps x Hcp Hr HE; exact (K4 cid ps x Hcp Hr HE)
  | exact Ha |].
  intros [Hw | Hw]; [exact (Hn Hw)|].
  destruct (PBELOW a Ha) as [Hx | Hx]; unfold CAT_STK, ESTACK in Hw; lia. }
assert (KEEP0 : forall a, kprot g pos mf nm tk dp a -> ~ (SF + V_cnt <= a < SF + V_cnt + 8) ->
  ~ (sh + 90 <= a < sh + 91) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1 H2. rewrite (KEEP1 a Ha H1). apply K0; [|exact H2 | exact H1].
  destruct (PBELOW a Ha) as [Hx | Hx]; lia. }
(* the machine-frame words the rest of the segment reads are where they were *)
assert (VKm : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= e_sp0 g ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk.
  apply KEEP0; [unfold kprot; left; lia | unfold V_cnt; lia | lia]. }
assert (P3 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr regs3 r = getr regs2 r) by (kc_pres HKR HP3).
(* ---- 0x81fb0 .. 0x81fe0: the row, and the call of reac_box_catalogue_defect ---- *)
set (row := SlotModel.t_row (e_pl g)) in *.
assert (Hrow : 0 <= row < 256) by (unfold row, SlotModel.t_row, SlotModel.tb; apply SlotModel.inb_range).
unfold BOX_COUNT in Vcnt.
remember (Eimg (Ereg regs3 [Z_to_bv 64 row])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply Eimg_env).
assert (ER1 : regs_ok E1 sr_atoms regs3) by (rewrite HE1; apply regs_ok_Eimg_Ereg).
assert (AGE1 : env_agree 32 (Ereg regs3 [Z_to_bv 64 row]) E1)
  by (rewrite HE1; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs3 r)
  by (intros n r Hn; rewrite HE1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1r : ew E1 32 = Z_to_bv 64 row)
  by (rewrite HE1, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
clear HE1.
assert (U9b : bv_unsigned (ew E1 9) = mf)
by (rewrite (EE1 9%nat 9%bv eq_refl), (P3 9%bv ltac:(cbn; tauto)), Rs1; apply unsigned_lit_small; lia).
assert (U18b : bv_unsigned (ew E1 18) = SF + V_cnt)
by (rewrite (EE1 18%nat 18%bv eq_refl), (P3 18%bv ltac:(cbn; tauto)), R18;
    apply unsigned_lit_small; unfold V_cnt; lia).
assert (HS1 : st_ok_pi SEGS VAL E1 kc_ss2
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + 0x18a4)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kc_ss2. apply pa_entry_st_ok_full.
  - exact ER1.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold kc_cntr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U18b. split; [unfold V_cnt; lia|]. split; [unfold V_cnt; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E1 _ (SF + V_cnt) 0 8 (SLit 11) 11);
      [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vcnt].
    + unfold kc_rowr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9b. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E1 _ mf 136 8 (SOff 32 0) row);
      [cbn [sv_denot]; rewrite E1r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      apply (VKm (mf + 136) 8%nat row ltac:(lia) ltac:(cbn; lia)). exact V136.
  - apply pairwise_disjoint_of_extents.
    unfold kc_cntr, kc_rowr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U18b, U9b. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold V_cnt. repeat split; try exact I; lia.
  - split; [exact I | split; [exact I | exact I]]. }
paj_run_shc RUNP RUNC HS1 HJ3.
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold kc_cntr, kc_rowr in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
(* the run read the count (11, so 0x81fb4 falls through) and the row index, and wrote nothing *)
assert (K1b : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha. apply (kept_of_frame E1 _ (w_H W2) mem3 (ms_mem ms0) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr. unfold windows in Hin. cbn in Hin.
  repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; cbn [base_val] in Hr; lia|]).
  destruct Hin. }
clear HF HFr HG.
assert (VKm1 : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= e_sp0 g ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms0)) a n v).
{ intros a n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact (VKm a n v H0 H1 Hv)].
  intros kk Hkk. apply K1b. lia. }
prreg HS1 (1%bv : bv 5) Q1b. prreg HS1 (10%bv : bv 5) Q10b. prreg HS1 (11%bv : bv 5) Q11b.
prreg HS1 (12%bv : bv 5) Q12b. prreg HS1 (13%bv : bv 5) Q13b.
pose proof (regs_kept_of_st_ok SEGS E1 _ (restrict (w_H W2) ms0) regs3 [Z_to_bv 64 row]
  [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 25; 26; 27]%bv HS1 AGE1 ltac:(vm_compute; reflexivity)) as HKR1.
cbn [ms_regs restrict] in HKR1.
kc_prreg_raw HS1 (10%bv : bv 5) Q10r. clear Q10b.
(* the catalogue row the entry reads, from HIMG's catalogue clause at the call state *)
assert (Haro4 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) (ms_mem ms0))).
{ apply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
    (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 (ms_mem ms0) _ _ HJ3). apply HRO. exact HROS. }
destruct (HIMG W2 (ms_mem ms0) Haro4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcat8 & Hrows).
assert (Hrr : 0 <= row mod 11 < 11) by (apply Z.mod_pos_bound; lia).
destruct (Hrows (row mod 11) ltac:(unfold BOX_COUNT; lia))
  as (Hlo & Hhi & Hd1 & Hd30 & I & O & P & sP & HIr & HOr & HPr & VP & VI & VO & Hrostr).
pose proof (pa_obj_img 27 ltac:(lia)) as Hcatb.
assert (E10c : ew E1 10 = Z_to_bv 64 (VAL (A_OBJ 27)))
  by (rewrite (EE1 10%nat 10%bv eq_refl), R10c; reflexivity).
pose proof (kc_e_denot E1 (VAL (A_OBJ 27)) row E10c E1r ltac:(lia) Hrow) as [De1 De2].
remember (VAL (A_OBJ 27) + 296 * (row mod 11)) as ee eqn:Eee in *.
assert (R10e : getr (ms_regs ms0) 10 = w64 ee) by (rewrite Q10r, denot_lit_U; unfold w64; f_equal; exact De1).
assert (R11e : getr (ms_regs ms0) 11 = w64 (SlotModel.t_in (e_pl g)))
  by (rewrite Q11b, (EE1 24%nat 24%bv eq_refl), (P3 24%bv ltac:(cbn; tauto)); exact R24).
assert (R12e : getr (ms_regs ms0) 12 = w64 (SlotModel.t_out (e_pl g)))
  by (rewrite Q12b, (EE1 25%nat 25%bv eq_refl), (P3 25%bv ltac:(cbn; tauto)); exact R25).
assert (R13e : getr (ms_regs ms0) 13 = w64 dp)
  by (rewrite Q13b, (EE1 22%nat 22%bv eq_refl), (P3 22%bv ltac:(cbn; tauto)); exact R22).
(* the display buffer: n_EXP_DP and a NUL, no zero byte inside, room for both in dp *)
destruct (k_r0 (e_pl g) Hr0) as [Hwok Hfits].
destruct (k_fits (e_pl g) Hfits) as (_ & _ & Hld). unfold SlotModel.n_ld in Hld.
pose proof (k_exp_dp_nz (e_pl g) Hwok) as Hdnz.
destruct (SlotModel.wok_chans (e_pl g) Hwok) as [Hin40 Hout40].
remember (SlotModel.n_EXP_DP (e_pl g)) as sd eqn:Esd in *.
assert (Hdpin : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (k_blocks g nm tk dp))
  by (unfold k_blocks; right; right; left; reflexivity).
destruct (HBbd _ _ Hdpin) as (Hdp4096 & Hdpce).
pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof HJ3 as (HAR3 & _).
assert (BKEEP : forall b n j, In (b, n) (k_blocks g nm tk dp) -> 0 <= j < req_size n ->
  aview SEGS (w_H W2) (ms_mem ms0) (b + j) = aview SEGS (w_H W2) mem2 (b + j)).
{ intros b n j Hbn Hj. destruct (HBbd b n Hbn) as (Hb1 & Hb2).
  rewrite K1b by lia. apply KEEP0.
  - unfold kprot, koutb. right; right; right. exists b, n, j. auto.
  - intros X. apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 _ _ b n j 4 pos HAR3 (HBin b n Hbn) Hin4 Hj).
    left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4) with 1024.
    unfold V_cnt in X. lia.
  - intros X. apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 _ _ b n j 4 pos HAR3 (HBin b n Hbn) Hin4 Hj).
    right. unfold in_zr. cbn [fst snd]. rewrite EFA. fold sh. change (fs_frame_bytes 4 / 8) with 128. lia. }
assert (Hdpb0 : bytes_at8 W2 (ms_mem ms0) dp (sd ++ [zb 0])).
{ unfold bytes_at8 in *. apply (k_garr8_moved W2 mem2 (ms_mem ms0) _ _); [|exact Hdpb].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk.
  apply (BKEEP dp _ kk Hdpin). lia. }
assert (HHP : catd_hpstr B ly2 S2 W2 (ms_mem ms0) dp sd).
{ split; [rewrite <- kc_lz; exact Hdpb0|]. split; [apply kc_nzl_notin; exact Hdnz|].
  exists (Z.max (SlotModel.t_cap_disp (e_pl g)) 1). split; [exact (HBin _ _ Hdpin) | lia]. }
(* the call chain and the stack of the call *)
assert (Hs0t : s0Z (ms_regs ms0) = e_sp0 g).
{ unfold s0Z. rewrite (HKR1 8%bv ltac:(cbn; tauto)), (P3 8%bv ltac:(cbn; tauto)), Rs0.
  unfold w64, e_sp0, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Usp1 : spZ (ms_regs ms0) = mf).
{ unfold spZ. rewrite (HKR1 2%bv ltac:(cbn; tauto)), (P3 2%bv ltac:(cbn; tauto)), Rsp.
  unfold w64. apply unsigned_lit_small. lia. }
destruct (kc_chain g pos ly2 S2 W2 (ms_mem ms0) _ _ mf HPRE HJ3 Hmfb
  (VKm1 (e_sp0 g - 8) 8%nat RA_LLVMF ltac:(lia) ltac:(lia) Vra)
  (VKm1 (e_sp0 g - 16) 8%nat (s0Z (e_regs g)) ltac:(lia) ltac:(lia) Vs0)) as (ch & Hach).
pmkst HS1. rewrite (PSIG IS_reac_box_catalogue_defect AF_reac_box_catalogue_defect eq_refl).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W2 (ms_regs ms0) (ms_mem ms0) (Z_to_bv 64 (BASE + AF_reac_box_catalogue_defect))
    LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ _
    REAC_BOX_CATALOGUE_DEFECT_STK [] 0 (mf - e_sp0 g) (getr (ms_regs ms0) 1) ch
    (fun ly' S' W' regs' mem' (_ : Model) =>
       getr regs' 10 = w64 (reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK ee (SlotModel.t_in (e_pl g))
         (SlotModel.t_out (e_pl g)) dp I O P sP sd) /\
       ly' = ly2 /\ S' = S2 /\ W' = W2 /\ Permutation (ablocks B ly' S') (ablocks B ly2 S2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms0) - REAC_BOX_CATALOGUE_DEFECT_STK <= a < spZ (ms_regs ms0)) ->
        aview SEGS (w_H W') mem' a = aview SEGS (w_H W2) (ms_mem ms0) a)) HJ3).
  - rewrite Usp1. ring.
  - pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2.
    rewrite Hmf32, Z.add_0_r in D1. rewrite Hsp16, Z.add_0_r in D2.
    replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK. lia.
  - unfold REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK. lia.
  - rewrite (HKR1 3%bv ltac:(cbn; tauto)), (P3 3%bv ltac:(cbn; tauto)). exact Rgp.
  - rewrite (HKR1 4%bv ltac:(cbn; tauto)), (P3 4%bv ltac:(cbn; tauto)). exact Rtp.
  - reflexivity.
  - rewrite Q1b. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1b, unsigned_lit_small by lia. lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by ring. rewrite Hs0t. exact Hach.
  - intros HPRE1.
    apply (HCATD ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ ch ee (SlotModel.t_in (e_pl g))
      (SlotModel.t_out (e_pl g)) dp I O P sP sd HPRE1 R10e R11e R12e R13e); try lia.
    + intros _. split; [lia|]. split; [lia|]. split.
      * exists (VAL (A_OBJ 27)), 3256. split; [exact G_CAT | lia].
      * split; [exact Hd1|]. split; [exact Hd30|]. split; [exact VP|]. split; [exact VI | exact VO].
    + intros _ _ HP0. split; [exact (Hrostr HP0) | exact HHP].
  - intros a (rg & [] & _). }
cbv beta. intros W4 c4 Hwle4
  (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJ1 & HP4 & (Rmask & -> & -> & -> & HPerm4 & KEEPD)).
rewrite Z.add_0_r in HJ4. rewrite Usp1 in KEEPD. clear HJ1.
(* ---- back at 0x81fe4: what the defect call kept, and the tail ---- *)
assert (KD : forall a, 0 <= a < 2 ^ 64 -> a < mf - 8208 ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) (ms_mem ms0) a)
  by (intros a Ha Ha2; apply KEEPD; [exact Ha | unfold REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK; lia]).
assert (P4m : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr regs4 r = getr (ms_regs ms0) r) by (kc_pres0 HP4).
kc_prreg_raw HS1 (20%bv : bv 5) Q20r. prreg HS1 (23%bv : bv 5) Q23b.
assert (R20c : getr regs4 20 = w64 ee)
  by (rewrite (P4m 20%bv ltac:(cbn; tauto)), Q20r, denot_lit_U; unfold w64; f_equal; exact De2).
assert (R23c : getr regs4 23 = w64 (VAL (A_OBJ 27)))
  by (rewrite (P4m 23%bv ltac:(cbn; tauto)), Q23b; exact E10c).
assert (RS4 : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 21; 22; 24; 25]%bv -> getr regs4 r = getr regs2 r).
{ intros r Hr. rewrite (P4m r ltac:(revert Hr; cbn [In]; tauto)), (HKR1 r ltac:(revert Hr; cbn [In]; tauto)).
  apply P3. revert Hr. cbn [In]. tauto. }
assert (KP4 : forall a, kprot g pos mf nm tk dp a -> ~ (SF + V_cnt <= a < SF + V_cnt + 8) ->
  ~ (sh + 90 <= a < sh + 91) -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1 H2. destruct (PBELOW a Ha) as [Hx | Hx].
  - rewrite (KEEPD a ltac:(lia) ltac:(lia)), K1b by lia. exact (KEEP0 a Ha H1 H2).
  - rewrite (KD a ltac:(lia) ltac:(lia)), K1b by lia. exact (KEEP0 a Ha H1 H2). }
assert (MK : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= mf - 8208 ->
  val_mem SEGS (rd W2 (ms_mem ms0)) a n v -> val_mem SEGS (rd W2 mem4) a n v).
{ intros a n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk. apply KD; lia. }
assert (GK : forall a l, 0 <= a -> a + Z.of_nat (length l) <= mf - 8208 ->
  garr8 SEGS (rd W2 (ms_mem ms0)) a l -> garr8 SEGS (rd W2 mem4) a l).
{ intros a l H0 H1 Hg. apply (k_garr8_moved W2 (ms_mem ms0) mem4 a l); [|exact Hg].
  intros kk Hkk. apply KD; lia. }
subst sd. rewrite Q1b.
apply (kc_tail g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 ee (row mod 11) I O P sP
  Hfrs Hk MLE MOK HC Hbl Hr0 R21 R22 R24 R25 V184 HJ4 RS4 R20c R23c Rmask KP4); try lia.
- unfold bytes_at8 in *. apply GK; [lia | rewrite length_map, length_app; cbn [length]; lia | exact Hdpb0].
- apply MK; [lia | cbn; lia | exact VP].
- apply MK; [lia | cbn; lia | exact VI].
- apply MK; [lia | cbn; lia | exact VO].
- intros HP0. destruct (Hrostr HP0) as (GP & NP & GLP & LoP & HiP).
  split; [|split; [exact NP | split; [exact GLP | split; [exact LoP | exact HiP]]]].
  apply GK; [lia | rewrite catd_lz_len; lia | exact GP].
Qed.
End c.
End b.
End a.
