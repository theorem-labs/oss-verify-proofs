(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B11b's snprintf call
   (0x88b9c `jal wrapper_snprintf`, return 0x88ba0), one pass of the join loop: the step pb11_snp from the call
   state to the return state at the FP state the wrapper returns. The B11b segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B11b, the snprintf step; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; reuse verdict none).
   ADAPTED from plugin-hostd/fuzz_command's released lib/A/Prog/check_reply_s4.v (origin/ossv/recipes 501c0d516c69,
   cr_s4: the snprintf call step of check_reply's walk: ecall_pre_stk_at, aj_art_own_atF with the destination in the
   walk's own class-5 frame, srr_art_postF_of_pf, srr_after_artF).

   THE CALL (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s 0x88b84-0x88b9c), pass ti of the join loop
   (0 <= ti < 11), sp = s1:
     snprintf(known + kn, 240 - kn, "%s%s", sep, tok)
     a0 = F + 0x320 + kn (slot 0x78 + s11), a1 = 240 - kn, a2 = 0x21820 "%s%s", a3 = 0x21860 "" (ti = 0) or 0x21840
     "|" (ti > 0), a4 = tp = the word at row ti of fuzz_catalogue (catA + 296 ti), whose bytes are token ti
     (sa_cat); ra = 0x88ba0.
   The text T = sep ++ tok has at most 12 bytes and 240 - kn >= 163, so snprintf writes all of it and its NUL at
   known + kn (sn_bytes / sn_len), returns |T| in a0, and keeps every byte off [s1 - CMD_SNP_K, s1) and off the
   written cells. The call's facts: the window CMD_SNP_K = 8192 below s1 lies in parse_file's own 12832-byte window
   (s1 >= sp0 - 383); the destination lies in the walk's class-5 frame (known in scope, PF_SC_KNOWN), off the
   image; the format and the separator are literals of PARSE_FILE_LITS (pf_obj), the token a literal of sa_cat;
   the stack-protector cells from pf_obj's sa_ssp; the rounding mode from pf_fi's sa_frm0.
   SECTION HYPOTHESIS: ASNPRINTF (pf_pieces.v's for B11b: RtFormat.asnprintf_realizes at
   pa_sigma SS___interceptor_trampoline_snprintf, gotwA, guardA, at every FP state).
   THE PROOF: pb11_jal steps the jal (the listing's PCall slot, pa_cert); then cr_s4's route: ecall_pre_stk_at,
   aj_art_own_atF (the destination is in the journal's own class-5 frame), srr_art_postF_of_pf, ASNPRINTF with the
   format family FR_cmd proved directly (two %s arguments, each a literal: pb11_lit_facts), srr_after_artF, and the
   statement's continuation at the returned FP state. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFPf RtPFShared RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B11b_d pf_seg_B11b_f pf_seg_B11b_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* the jal writes ra; every register the call reads is another one *)
Ltac pb11_n1 := intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate Hc.
Lemma pb11_cs_n1 : forall r : Z, acallee_saved r -> Z_to_bv 5 r <> (1%bv : bv 5).
Proof.
intros r H Hc. apply (f_equal bv_unsigned) in Hc.
rewrite Z_to_bv_unsigned in Hc. unfold bv_wrap in Hc. change (bv_modulus 5) with 32 in Hc.
assert (E : bv_unsigned (1%bv : bv 5) = 1) by (vm_compute; reflexivity). rewrite E in Hc.
unfold acallee_saved in H. lia.
Qed.
(* a disjointness of two ranges the call names, by arithmetic over the call's numbers *)
Ltac pb11_disj := unfold zdisjoint; cbn [fst snd]; unfold kImgEnd, gotwA, guardA; lia.
Ltac pb11_two := constructor; [pb11_disj | constructor; [pb11_disj | constructor]].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* 0x88b9c `jal wrapper_snprintf`: the listing's slot is PCall SS___interceptor_trampoline_snprintf ra (pa_cert),
   so one step sets ra = 0x88ba0 and jumps to the trampoline; the model is the step's materialized one *)
Lemma pb11_jal : forall (W : world SEGS) (regs : bvmap 5 word) mem md (Q : world SEGS -> config -> Prop),
  (forall mat', SRr SEGS W (mkCfg (mkst (regupd regs (1%bv : bv 5) (w64 (BASE + PF_KSRET)))
     (w64 (pa_sigma SS___interceptor_trampoline_snprintf)) mem (seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + PF_KSNP) regs mem md) Q.
Proof.
intros W regs mem md Q HK.
assert (Hpl : plookup (@pl_tpi seg_listing PL_seg) PF_KSNP =
  Some (PCall SS___interceptor_trampoline_snprintf (1%bv : bv 5))) by (vm_compute; reflexivity).
rewrite <- (@pl_tpi_eq seg_listing PL_seg) in Hpl.
pose proof (cert_slot ssym (clookup pa_tbl) pa_val pa_sigma seg_listing pa_cert _ _ Hpl) as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (pa_val A_TEXT + PF_KSNP)) as [wz|] eqn:Hl; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd _]. apply reg_eqb_eq in Hrd. subst.
apply Z.eqb_eq in Ht.
pose proof pa_B_ok as (HB0 & HB1 & _).
assert (Hk : PF_KSNP = 15836) by reflexivity.
assert (Hr : PF_KSRET = 15840) by reflexivity.
unfold cfg_at, w64.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  exact (step_jal_link SEGS _ _ _ _ _ _ _ (pa_fetch_ok _ _ Hl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate))
    Hdec).
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (pa_val A_TEXT + PF_KSNP)) 4) with (Z_to_bv 64 (pa_val A_TEXT + PF_KSRET))
    by (unfold v_addi; rewrite unsigned_lit_small by lia; f_equal; lia).
  lazymatch goal with |- context [btgt ?pc (bv_signed ?im)] =>
    replace (btgt pc (bv_signed im)) with (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_snprintf))
      by (unfold btgt, v_addi; rewrite unsigned_lit_small by lia; rewrite <- Ht, lit_canon; reflexivity)
  end.
  exact (HK _).
Qed.

(* a .rodata literal passed to snprintf (the format "%s%s", the separator, the token): its bytes at the call's
   reader (rd0 = the cut's reader, which the call's agrees with), its slack (ROM), its shadow (sa_pinned at the
   call's AR state), and its place in the image, below every region the call writes *)
Lemma pb11_lit_facts : forall ly S (W : world SEGS) mem md (rd0 : reader) w s (rs : list (Z * Z)),
  AR SEGS B ly S W mem md -> sa_lit SEGS B rd0 w s -> (forall a, rdW W mem a = rd0 a) ->
  Forall (fun r => kImgEnd + 8 <= fst r \/ fst r + snd r <= 0x10000) rs ->
  0 < w /\ 0x10000 <= w /\ w + Z.of_nat (length s) < kImgEnd /\
  (forall i, 0 <= i <= Z.of_nat (length s) -> rdW W mem (w + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) /\
  (forall x, w + Z.of_nat (length s) < x < RtPFShared.str_end w s -> rdW W mem x <> None) /\
  Forall (zdisjoint (w, RtPFShared.str_end w s - w)) rs /\
  Forall (zdisjoint (w, Z.of_nat (length s) + 1)) rs /\
  amem_range w (RtPFShared.str_end w s - w) /\ amem_range w (Z.of_nat (length s) + 8) /\
  amem_range w (Z.of_nat (length s) + 1) /\
  range_addressable (rdW W mem) SHADOW_OFF w (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (rdW W mem) w (Z.of_nat (length s) + 1).
Proof.
intros ly S W mem md rd0 w s rs HAR (Hw & ((Hz & _) & _) & Hpin & Hrt & Himg) EQ Hrs.
destruct (Hpin ly S W mem md HAR) as (_ & _ & _ & A3 & A4).
pose proof (pa_img_range _ (proj1 (Himg w ltac:(lia)))) as Rw.
pose proof (pa_img_range _ (proj1 (Himg (w + Z.of_nat (length s)) ltac:(lia)))) as Re.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
assert (HSE : w + Z.of_nat (length s) + 1 <= RtPFShared.str_end w s <= w + Z.of_nat (length s) + 8)
  by (unfold RtPFShared.str_end; lia).
unfold kImgEnd in *.
assert (HD : forall n, 0 <= n <= RtPFShared.str_end w s - w -> Forall (zdisjoint (w, n)) rs).
{ intros n Hn. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as H.
  cbv beta in H. unfold zdisjoint. cbn [fst snd]. lia. }
split; [exact Hw|]. split; [lia|]. split; [lia|].
split.
{ intros i Hi. rewrite EQ. replace (w + i) with (w + Z.of_nat (Z.to_nat i)) by lia. apply Hz.
  rewrite length_app. cbn [length]. lia. }
split.
{ intros x Hx. exact (sa_tail_of_romtail SEGS (w_H W) mem _ Hrt x ltac:(unfold RtPFShared.str_end in Hx; lia)). }
split; [apply HD; lia|]. split; [apply HD; lia|].
split; [unfold amem_range, kLowMemEnd; lia|]. split; [unfold amem_range, kLowMemEnd; lia|].
split; [unfold amem_range, kLowMemEnd; lia|].
split; [exact A3 | apply A4; lia].
Qed.
(* the call of pass ti: the state at KLOOP (INV_KLOOP at memc), the call state's memory memS (the run from KLOOP
   stores nothing, so memS shows memc's bytes) with the journal at memS, and the call's registers. The step ends
   at the return 0x88ba0 at the FP state f1 the wrapper returns: known + kn holds the text and its NUL, a0 = |T|,
   the callee-saved registers are kept, the journal holds at the new memory, and every other byte off the window
   is memc's. *)
Lemma pb11_snp : forall n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val rS memS mdS tp,
  INV_KLOOP B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memS mdS 0 ->
  (forall a, rdW Wc memS a = rdW Wc memc a) ->
  getr rS 2 = w64 (pf_s1 v) ->
  getr rS 3 = w64 (as_gp B) -> getr rS 4 = w64 (as_tp B) ->
  getr rS 10 = w64 (pf_F v pos + PF_O_KNOWN + pb11_kn ti) -> getr rS 11 = w64 (240 - pb11_kn ti) ->
  getr rS 12 = w64 (seg_litA_rc F_ss) -> getr rS 13 = w64 (seg_litA_rc (pb11_sep ti)) -> getr rS 14 = w64 tp ->
  rdword (rdW Wc memc) (pin_spec.row_addr catA ti) = Some tp ->
  sa_lit SEGS B (rdW Wc memc) tp (seg_spec.zs (pin_spec.tok_bytes ti)) ->
  (forall (f1 : YK11.FPState) regs2 mem2 md2, fxrel fx f1 ->
     ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
       (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mem2 md2 0 ->
     aregs_preserved rS regs2 ->
     getr regs2 10 = w64 (Z.of_nat (length (pb11_text ti))) ->
     sa_zs (rdW Wc mem2) (pf_F v pos + PF_O_KNOWN + pb11_kn ti) (pb11_text ti ++ [0]) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - RtPFCmd.CMD_SNP_K <= a < pf_s1 v) ->
        ~ (pf_F v pos + PF_O_KNOWN + pb11_kn ti <= a <
           pf_F v pos + PF_O_KNOWN + pb11_kn ti + Z.of_nat (length (pb11_text ti)) + 1) ->
        rdW Wc mem2 a = rdW Wc memc a) ->
     SRr SEGS Wc (mkCfg (@mkst f1 regs2 (w64 (BASE + PF_KSRET)) mem2 (seg_rom SEGS)) md2)
       (PB11_POST (fx := f1) B v cf gi nm val o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KSNP) rS memS mdS) (PB11_POST B v cf gi nm val o ln).
Proof.
intros n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val rS memS mdS tp
  HK HJ EQV R2 R3 R4 R10 R11 R12 R13 R14 _ HLIT KONT.
destruct HK as (HB & _ & _ & _ & _ & Hti & _ & _ & _ & _).
pose proof (pb11_geo B _ _ _ _ _ _ _ _ _ HB) as (_ & Hly & Hin & G & _ & _).
pose proof (pb11_rom B _ _ _ _ _ _ _ _ _ HB) as HROM.
pose proof HB as (_ & HFI & HOBJ & _ & HFSH).
destruct HFI as (_ & _ & _ & _ & _ & _ & HFRM & _ & _ & _).
destruct HOBJ as (_ & _ & _ & _ & _ & _ & LI & _ & SS).
destruct SS as (SG1 & cval & SG2).
subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
pose proof STK_values as (_ & _ & _ & SPF & _).
rewrite SPF in G1. unfold kImgEnd in G13.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & _).
assert (Hti10 : (ti <= 10)%nat) by lia.
assert (Hkn : 0 <= pb11_kn ti <= 77) by (apply pb11_kn_bound; lia).
assert (HTl : 5 <= Z.of_nat (length (pb11_text ti)) <= 12).
{ unfold pb11_text. rewrite length_app. pose proof (pb11_sep_len ti). pose proof (pb11_tok_len ti Hti10). lia. }
assert (EOK : PF_O_KNOWN = 0x320) by reflexivity.
assert (HK : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
assert (HKR : PF_KSRET = 15840) by reflexivity.
pose proof (proj1 HJ) as HARS.
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HARS Hin) as (_ & _ & HFpS & _).
change (fs_frame_bytes 5) with 2048 in HFpS. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in HFpS.
(* the text: at most 12 bytes, so snprintf writes all of it and its NUL (240 - kn - 1 >= 162) *)
assert (Hsn : RtPFShared.sn_bytes (240 - pb11_kn ti - 1) (pb11_text ti) = pb11_text ti ++ [0]).
{ unfold RtPFShared.sn_bytes. rewrite firstn_all2; [reflexivity | lia]. }
assert (Hsl : RtPFShared.sn_len (240 - pb11_kn ti - 1) (pb11_text ti) = Z.of_nat (length (pb11_text ti)) + 1).
{ unfold RtPFShared.sn_len. rewrite Hsn, length_app. cbn [length]. lia. }
(* 0x88b9c: the jal *)
apply pb11_jal. intros mat'.
set (mdv := with_vm_backing (m_vm_lazy mdS) mat' mdS).
set (regsT := regupd rS (1%bv : bv 5) (w64 (BASE + PF_KSRET))).
pose proof (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ) as HJT.
assert (RT1 : getr regsT (1%bv : bv 5) = w64 (BASE + PF_KSRET)).
{ unfold regsT. apply getr_same.
  intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc. }
assert (RT : forall r : bv 5, r <> (1%bv : bv 5) -> getr regsT r = getr rS r).
{ intros r Hne. unfold regsT. apply getr_other. exact Hne. }
assert (HspS : spZ regsT = pf_s1 v).
{ unfold spZ. rewrite (RT (2%bv : bv 5) ltac:(pb11_n1)), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (HspT : spZ regsT = pf_sp0 v + (pf_s1 v - pf_sp0 v)) by lia.
assert (Ho16 : (pf_s1 v - pf_sp0 v) mod 16 = 0).
{ pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D2.
  rewrite G5, Z.add_0_r in D1. rewrite G3, Z.add_0_r in D2.
  replace (pf_s1 v - pf_sp0 v) with ((2 * (pf_s1 v / 32) - pf_sp0 v / 16) * 16) by lia. apply Z_mod_mult. }
assert (HraT : YK0s.ret_ok (getr regsT 1)).
{ rewrite RT1. exact (ret_ok_codeptr_v PF_KSRET ltac:(lia) ltac:(rewrite HKR; reflexivity)). }
destruct (ecall_pre_stk_at SEGS B RtPFCmd.CMD_SNP_K STK_reac_segconf_parse_file (pf_sp0 v)
  (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc Wc memS mdv 0
  regsT (pf_s1 v - pf_sp0 v) HJT HspT Ho16 ltac:(lia) ltac:(rewrite HK; unfold ESTACK; lia)
  ltac:(rewrite HK, SPF; lia) HraT ltac:(rewrite (RT (3%bv : bv 5) ltac:(pb11_n1)); exact R3)
  ltac:(rewrite (RT (4%bv : bv 5) ltac:(pb11_n1)); exact R4))
  as (EPRE & ESTK & EPRES).
(* the literals: the format "%s%s" and the separator (PARSE_FILE_LITS), the token (sa_cat's row ti) *)
assert (RW : forall a, rdword (rdW Wc memS) a = rdword (rdW Wc memc) a)
  by (intros a; unfold rdword; rewrite !EQV; reflexivity).
rewrite (pb11_tok_cat ti Hti) in HLIT.
assert (HRS : Forall (fun r => kImgEnd + 8 <= fst r \/ fst r + snd r <= 0x10000)
  (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ regsT) (pf_F v pos + PF_O_KNOWN + pb11_kn ti)
     (RtPFShared.sn_len (240 - pb11_kn ti - 1) (pb11_text ti)))).
{ unfold RtPFShared.snp_out. rewrite HspS, HK, Hsl. unfold kImgEnd.
  constructor; [cbn [fst snd]; lia | constructor; [cbn [fst snd]; lia | constructor]]. }
pose proof (pb11_lit_facts _ _ _ _ _ _ _ _ _ HARS (LI F_ss pb11_in_lits_ss) EQV HRS)
  as (Fl1 & Fl2 & Fl3 & FlB & _ & _ & FlD & _ & _ & FlA & FlR & FlH).
pose proof (pb11_lit_facts _ _ _ _ _ _ _ _ _ HARS (LI (pb11_sep ti) (pb11_in_lits_sep ti)) EQV HRS)
  as (Sl1 & Sl2 & Sl3 & SlB & SlT & SlD & _ & SlS & SlM & SlA & SlR & SlH).
pose proof (pb11_lit_facts _ _ _ _ _ _ _ _ _ HARS HLIT EQV HRS)
  as (Tl1 & Tl2 & Tl3 & TlB & TlT & TlD & _ & TlS & TlM & TlA & TlR & TlH).
unfold kImgEnd in Fl3, Sl3, Tl3.
assert (A3 : argZ regsT 3 = seg_litA_rc (pb11_sep ti)).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite (RT (13%bv : bv 5) ltac:(pb11_n1)), R13. unfold w64. apply unsigned_lit_small. lia. }
assert (A4 : argZ regsT 4 = tp).
{ unfold argZ. replace (Z_to_bv 5 (10 + 4)) with (14%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite (RT (14%bv : bv 5) ltac:(pb11_n1)), R14. unfold w64. apply unsigned_lit_small. lia. }
assert (LF : length F_ss = 4%nat) by (vm_compute; reflexivity).
(* 0x88b9c: snprintf(known + kn, 240 - kn, "%s%s", sep, tok) writes the text into known (the class-5 frame) *)
unfold PB11_POST, pf_postm, PF_POSTr.
eapply srr_after_artF.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFCmd.CMD_SNP_K
    (fun a => pf_F v pos + PF_O_KNOWN + pb11_kn ti <= a <
       pf_F v pos + PF_O_KNOWN + pb11_kn ti + RtPFShared.sn_len (240 - pb11_kn ti - 1) (pb11_text ti))
    (pa_sigma SS___interceptor_trampoline_snprintf) Wc regsT memS STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc mdv 0
    (pf_s1 v - pf_sp0 v) (w64 (BASE + PF_KSRET)) _ HJT HspT Ho16 ltac:(lia) ltac:(rewrite HK; lia)
    ltac:(rewrite HK, SPF; lia) ltac:(exact RT1)).
  - intros a Ha. cbv beta in Ha. rewrite Hsl in Ha. unfold awr_byte. right; right; right; left.
    exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (fs_frame_bytes 5) with 2048. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). lia.
  - apply srr_art_postF_of_pf; [exact EPRES|].
    apply (ASNPRINTF fx (p_ly v) Sc Wc regsT memS mdv (pf_F v pos + PF_O_KNOWN + pb11_kn ti) (240 - pb11_kn ti)
      (seg_litA_rc F_ss) [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) (pb11_text ti) cval).
    + exact EPRE.
    + exact ESTK.
    + exact EPRES.
    + rewrite (RT (10%bv : bv 5) ltac:(pb11_n1)). exact R10.
    + rewrite (RT (11%bv : bv 5) ltac:(pb11_n1)). exact R11.
    + rewrite (RT (12%bv : bv 5) ltac:(pb11_n1)). exact R12.
    + intros a H1 H2 H3. rewrite EQV. exact (HROM a H1 H2 H3).
    + apply Forall_forall. intros r Hr. unfold RtPFCmd.CMD_SNP_CR in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [cbn [fst snd]; lia |]). destruct Hr.
    + apply Forall_forall. intros r Hr. cbv beta. unfold RtPFCmd.CMD_SNP_CR in Hr. cbn [In] in Hr.
      unfold RtPFShared.snp_out. rewrite HspS, HK, Hsl.
      repeat (destruct Hr as [<- | Hr]; [pb11_two |]). destruct Hr.
    + rewrite RW. exact SG1.
    + rewrite RW. exact SG2.
    + unfold gotwA; lia.
    + unfold gotwA; lia.
    + unfold guardA; lia.
    + unfold guardA; lia.
    + unfold RtPFShared.snp_out. rewrite HspS, HK, Hsl. pb11_two.
    + unfold RtPFShared.snp_out. rewrite HspS, HK, Hsl. pb11_two.
    + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
    + cbn [length]. rewrite HspS. lia.
    + unfold RtPFShared.snp_out. rewrite HspS, HK, Hsl. cbn [length]. pb11_two.
    + (* the format family: "%s%s" with the separator and the token as its two strings *)
      unfold RtPFCmd.FR_cmd. cbv beta. cbn [map app]. rewrite A3, A4.
      exists F_ss, [RtPFPf.Ps; RtPFPf.Ps], [RtPFPf.APtr (pb11_sep ti); RtPFPf.APtr (pb11_tok ti)].
      refine (conj _ (conj _ (conj (RtPFCmd.pf_cmd_piece_all _) (conj _ (conj _ (conj _ (conj _ (conj _
        (conj _ (conj _ _)))))))))).
      * exact (conj Fl1 (conj FlB (conj FlD (conj FlA (conj FlR FlH))))).
      * vm_compute. reflexivity.
      * cbn [RtPFShared.pf_args_asan RtPFShared.pf_arg_asan].
        refine (conj (conj (pb11_sep_byte ti) (conj Sl1 (conj _ (conj SlB (conj SlT (conj SlD (conj SlA
          (conj SlR SlH))))))))
          (conj (conj (pb11_tok_byte ti Hti10) (conj Tl1 (conj _ (conj TlB (conj TlT (conj TlD (conj TlA
          (conj TlR TlH)))))))) I)); lia.
      * cbn [RtPFPf.pf_text option_map]. rewrite app_nil_r. reflexivity.
      * exact I.
      * rewrite pb11_lit_ss. unfold RtPFCmd.CMD_IMG_LO. lia.
      * rewrite pb11_lit_ss, LF. unfold RtPFCmd.CMD_GOTW. lia.
      * cbn [RtPFCmd.cmd_args_slack]. exact (conj SlS (conj TlS I)).
      * intros Hc. rewrite Hc in LF. discriminate LF.
      * cbn [RtPFCmd.cmd_args_amem]. exact (conj SlM (conj TlM I)).
    + lia.
    + lia.
    + lia.
    + rewrite Hsl. lia.
    + unfold RtPFShared.snp_out. rewrite HspS, HK, Hsl. cbn [pairwise].
      split; [constructor; [pb11_disj | constructor] | split; [constructor | exact I]].
    + intros a Ha. rewrite Hsl in Ha. destruct (HFpS a ltac:(lia)) as [Hp Hno].
      split; [exact (apresent_writable SEGS _ _ _ Hp)|]. split; [exact Hno|].
      rewrite HspS. unfold ESTACK. lia.
    + rewrite Hsl. exact (amem_range_sub_app (pf_F v pos) 2048 (pf_F v pos + PF_O_KNOWN + pb11_kn ti)
        (Z.of_nat (length (pb11_text ti)) + 1 + 8) G9 G7 ltac:(lia) ltac:(lia) ltac:(lia)).
    + (* known's 30 shadow cells (cells 100 .. 129 of the frame) are 0 in PF_SC_KNOWN *)
      rewrite Hsl. intros x Hx. exists 0. split; [| left; reflexivity].
      rewrite EQV.
      assert (Hi : 100 <= (x - pf_F v pos) / 8 < 130)
        by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
      pose proof (HFSH ((x - pf_F v pos) / 8) ltac:(lia)) as Hs.
      rewrite (pb11_shb_in _ (or_introl Hi)) in Hs.
      assert (E8 : x / 8 = pf_F v pos / 8 + (x - pf_F v pos) / 8)
        by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
      unfold shadow_of_addr. rewrite E8, Z.add_assoc, <- G10. exact Hs.
    + rewrite Hsl.
      exact (shadow_hull_vis_of_frame SEGS B LAWS (p_ly v) Sc Wc memS mdS 5 pos
        (pf_F v pos + PF_O_KNOWN + pb11_kn ti) (Z.of_nat (length (pb11_text ti)) + 1) HARS Hin
        ltac:(change (frame_addr (p_ly v) 5 pos) with (pf_F v pos); lia)
        ltac:(change (frame_addr (p_ly v) 5 pos) with (pf_F v pos); change (fs_frame_bytes 5) with 2048; lia)
        ltac:(lia)).
    + rewrite Hsl. unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI, kImgEnd. cbn [fst snd]. lia.
    + exact HFRM. }
(* back at 0x88ba0 at the FP state fx1 the wrapper returns *)
cbv beta. intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & (HA0 & HBY) & HK2).
apply (KONT fx1 regs2 mem2 md2 Hfx HJ2).
- intros r Hr. rewrite (HP2 r Hr). apply RT. exact (pb11_cs_n1 r Hr).
- exact HA0.
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite Hsl in HBY. specialize (HBY (Z.of_nat i) ltac:(lia)). rewrite Hsn, Nat2Z.id in HBY. exact HBY.
- intros a Ha Hw Hd. rewrite (HK2 a Ha ltac:(lia) ltac:(rewrite Hsl; lia)). apply EQV.
Qed.
End x.
End d.
