(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the four strcasecmp calls of segment A12 of
   reac_segconf_parse_file's walk (the ignore key, reac_segconf.c:271-280 with parse_bool R:88-99 inlined), part of
   segment A12's proof, by the G3 walk owner, 2026-10-30. No instruction is walked here.

   The four calls differ only in the literal (excerpt in the unit's internal record, commit dfb49d6ad789, path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s):
     0x88370 strcasecmp(val, "yes"   0x21b80)    0x88388 strcasecmp(val, "true"  0x21ba0)
     0x883d4 strcasecmp(val, "no"    0x21bc0)    0x883e8 strcasecmp(val, "false" 0x21be0)
   each with a0 = s9 = the value in buf, a1 = the literal's address, sp = pf_s1 v, through the trampoline
   SIGMA SS___interceptor_trampoline_strcasecmp. The contract is the interceptor owner's row 10, lib/A/Rt/RtSeg.v
   astrcasecmp_realizes (window 2 * ESTACK), taken as the Section hypothesis ASC at every FP state.

     a12_astr_of_sa   SegABase's sa_str (list Z) gives astr_at at seg_spec.zb l, zs (zb l) = l and
                      astr_len (zb l) = |l|.
     a12_sc_pre       the call from the cut alone: every premise of ASC from pf_base (ecall_pre_stk from the
                      journal by PaArt.ecall_pre_stk_at; the value's bytes, shadow and tail from the class-5 frame,
                      pf_a5_k.a5_geo and pf_a6_k.a6_buf_arg; the literal's from pf_obj's sa_lit; rt_rom_view from
                      pf_a5_k.a5_rom), and the wrapper's answer over the folds turned into SegModel.strcasecmp
                      by pf_a12_pure.a12_sc_of_fold and pf_a12_k.a12_lc_tolower.
     a12_sc_after     pf_base again at the call's new memory: pf_a5_k.a5_move0 at the same layout, state and
                      scope, the window [s1 - 2 * ESTACK, s1) being inside a5_Wrx's first disjunct
                      [sp0 - STK, s1) (STK_reac_segconf_parse_file = 12800, sp0 - 352 <= s1).

   The shapes of a12_astr_of_sa, of the value's and the literal's read facts and of the ecall_pre_stk step are
   segment A7's proof's (lib/A/Prog/pf_a7_r.v at commit
   ebe0b30cca65: a7_astr_of_sa, a7_str_some, a7_read_ok_of_addr, a7_tail_vis_buf, a7_ecall_pre_buf,
   a7_lit_read), restated over pf_base in place of A7's a7_st.

   Section hypotheses: ASC only (B is the symbols). No SSPX, no VRO, no ROMV. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a5_k pf_a6_k pf_a12_pure pf_a12_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require PaArt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* every byte of a C string and its NUL is mapped (pf_a7_r.v a7_str_some) *)
Lemma a12c_str_some : forall (rd : reader) p s a, sa_str rd p s -> p <= a <= p + Z.of_nat (length s) ->
  rd a <> None.
Proof.
  intros rd p s a [[Hz _] _] Ha.
  assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hz _ Hi) as E. rewrite Z2Nat.id in E by lia.
  replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
Qed.

(* the model state is its own frame-state update *)
Lemma a12c_set_fs_id : forall s, s = set_fs (st_fs s) s.
Proof. intros s. destruct s. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** The text bridge: sa_str (list Z) to astr_at (list byte) (pf_a7_r.v a7_astr_of_sa) *)
Lemma a12_astr_of_sa : forall (W : world SEGS) mem q l,
  sa_str (rdW W mem) q l ->
  astr_at SEGS W mem q (seg_spec.zb l) /\ seg_spec.zs (seg_spec.zb l) = l /\
  astr_len (seg_spec.zb l) = Z.of_nat (length l).
Proof.
  intros W mem q l [Hz _].
  destruct (sa_strz_bytes SEGS (w_H W) mem q l Hz) as (Hb & Hn & Hzs).
  split; [apply astr_atR_view; split; [exact Hb | exact Hn]|].
  split; [exact Hzs|].
  unfold astr_len, seg_spec.zb. rewrite length_map. reflexivity.
Qed.

(* a mapped byte stays mapped when its presence is kept (an image byte the memory does not hold reads the ROM
   at both memories) *)
Lemma a12c_view_kept : forall (H : word -> bool) (mem mem' : word -> option byte) a,
  (apresent H mem a -> apresent H mem' a) -> aview SEGS H mem a <> None -> aview SEGS H mem' a <> None.
Proof.
  intros H mem mem' a Hp. unfold apresent in Hp. unfold aview, mbyte, mrestrict. cbv beta.
  destruct (H (Z_to_bv 64 a)) eqn:Eh; [intros Hv; exact Hv|].
  destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Em.
  - intros _. destruct (Hp (conj eq_refl (ex_intro _ b eq_refl))) as [_ [b' Hb']]. rewrite Hb'. cbn. discriminate.
  - destruct (mem' (Z_to_bv 64 a)) as [b'|]; intros Hv; [cbn; discriminate | exact Hv].
Qed.

Section e.
Variable B : asyms.
(* the interceptor owner's row 10 (lib/A/Rt/RtSeg.v), at every FP state, at the listing's trampoline (the image-A owner's ruling
   16:54Z) *)
Hypothesis ASC : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strcasecmp).

(** ** The call's premises, from the cut alone *)
Lemma a12_sc_pre : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc (regsc : bvmap 5 word) vp val s,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  In s PARSE_FILE_LITS ->
  sa_str (rdW Wc memc) vp val -> pf_inb (pf_F v pos + PF_O_BUF) vp val ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 vp -> getr regsc 11 = w64 (seg_litA_rc s) ->
  SRr SEGS Wc (cfg_at SEGS (SIGMA SS___interceptor_trampoline_strcasecmp) regsc memc mdc)
    (art_post SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc (fun _ => False)
       (fun regs' _ => getr regs' 10 = w64 0 <-> SegModel.strcasecmp val s = 0)).
Proof.
  intros v pos lyc Sc Wc rX memc mdc regsc vp val s HB Hin Hstr Hinb Hsp Hra Hgp Htp H10 H11.
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & Hfp & _).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof STK_values as (_ & _ & _ & SPF & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite SPF in G1.
  pose proof Hinb as Hinb0.
  unfold pf_inb, PF_O_BUF in Hinb. destruct Hinb as [Hb1 Hb2].
  (* the value: its bytes, its shadow (buf in scope), its tail inside the frame *)
  destruct (a12_astr_of_sa Wc memc vp val Hstr) as (VA & VZ & VL).
  destruct (a6_buf_arg B v pos lyc Sc Wc rX memc mdc PF_SC_LINE vp val [] HB eq_refl eq_refl Hstr Hinb0
    ltac:(apply Forall_nil)) as (VARG & _).
  cbn [sa_va_arg] in VARG. destruct VARG as (_ & _ & _ & VADDR & _).
  rewrite (a6_w64_u vp) in VADDR by lia.
  assert (V0 : 0 < vp) by lia.
  assert (RDV : aread_ok SEGS (2 * ESTACK) Wc regsc memc vp (astr_len (seg_spec.zb val) + 1)).
  { rewrite VL. destruct VADDR as (A0 & A1 & A2 & A3 & A4).
    split; [exact A0|]. split; [exact A1|]. split; [lia|].
    split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
    intros a Ha. split; [apply (a12c_str_some _ _ _ a Hstr); lia|].
    unfold ascratch_stk. rewrite Hsp. unfold ESTACK. lia. }
  assert (AMV : amem_range vp (astr_len (seg_spec.zb val) + 8)).
  { rewrite VL. apply amem_range_high; [lia| |unfold ASAN_CEIL in *; lia].
    unfold in_app, kLowShadowBeg, YG0f.kHighMemBeg, ASAN_CEIL in G9.
    destruct G9 as [_ [Hlo | [Hhi1 Hhi2]]]; [left; lia | right; lia]. }
  assert (TV : atail_vis SEGS Wc memc (vp + astr_len (seg_spec.zb val))).
  { rewrite VL. intros a Ha.
    apply (aview_some_of_apresent SEGS). apply Hfp.
    pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D0.
    pose proof (Z.div_mod (vp + Z.of_nat (length val)) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (vp + Z.of_nat (length val)) 8 ltac:(lia)) as M1. lia. }
  (* the literal: sa_lit of pf_obj (sa_pinned at the state's AR, the image bytes, the ROM tail) *)
  pose proof HB as (_ & (HJ & _) & HOBJ & _).
  destruct HOBJ as (_ & _ & _ & _ & _ & _ & HL & _).
  destruct (HL s Hin) as (La0 & Lstr & Lpin & _ & Limg).
  destruct (a12_astr_of_sa Wc memc _ s Lstr) as (LA & LZ & LL).
  pose proof Lstr as (_ & LT).
  pose proof (Lpin lyc Sc Wc memc mdc HAR) as LADDR.
  pose proof (proj1 (Limg (seg_litA_rc s + Z.of_nat (length s)) ltac:(lia))) as Limg1.
  pose proof (pa_img_range _ Limg1) as Lrg. unfold kImgEnd in Lrg.
  assert (RDL : aread_ok SEGS (2 * ESTACK) Wc regsc memc (seg_litA_rc s) (astr_len (seg_spec.zb s) + 1)).
  { rewrite LL. destruct LADDR as (A0 & A1 & A2 & A3 & A4).
    split; [exact A0|]. split; [exact A1|]. split; [lia|].
    split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
    intros a Ha. split; [apply (a12c_str_some _ _ _ a Lstr); lia|].
    unfold ascratch_stk. rewrite Hsp. unfold ESTACK. lia. }
  assert (AML : amem_range (seg_litA_rc s) (astr_len (seg_spec.zb s) + 8)).
  { rewrite LL. unfold amem_range. left. rewrite C5. lia. }
  assert (TL : atail_vis SEGS Wc memc (seg_litA_rc s + astr_len (seg_spec.zb s))).
  { rewrite LL. exact LT. }
  (* the runtime-call pre-state at sp = s1 = sp0 + o, o in [-352, -320], a multiple of 16 *)
  assert (Hal : (pf_s1 v - pf_sp0 v) mod 16 = 0).
  { pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)). pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)).
    pose proof (Z.div_mod (pf_s1 v - pf_sp0 v) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (pf_s1 v - pf_sp0 v) 16 ltac:(lia)). lia. }
  assert (PRE : ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc).
  { apply (PaArt.ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0
      regsc (pf_s1 v - pf_sp0 v) HJ);
      [lia | exact Hal | lia | unfold ESTACK; lia | rewrite SPF; unfold ESTACK; lia
      | exact Hra | exact Hgp | exact Htp]. }
  (* the wrapper's answer over the folds is SegModel.strcasecmp of the two texts *)
  assert (LBV : a12_byte_vals s) by (rewrite <- LZ; exact (a12_vals_zs _ (proj2 LA))).
  pose proof (a12_sc_of_fold RtSeg.lc a12_lc_tolower (seg_spec.zb val) s (proj2 VA) LBV) as E.
  assert (IFF : map RtSeg.lc (seg_spec.zs (seg_spec.zb val) ++ [0]) =
                map RtSeg.lc (map bv_unsigned (map (Z_to_bv 8) s) ++ [0]) <-> SegModel.strcasecmp val s = 0).
  { split; intros HX.
    - pose proof (proj1 E HX) as HY. rewrite VZ in HY. exact HY.
    - apply (proj2 E). rewrite VZ. exact HX. }
  eapply SRr_mono.
  - exact (ASC fx lyc Sc Wc regsc memc mdc vp (seg_litA_rc s) (seg_spec.zb val) (seg_spec.zb s)
      PRE H10 H11 V0 La0 VA LA RDV AMV RDL AML TV TL (a5_rom B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB)).
  - intros W' c' _ HP. unfold art_post in HP |- *.
    destruct HP as (HW & regs' & mem' & md' & Hc & HAR' & Hpr & Hsm & HQ & HK & HP1 & HP2).
    split; [exact HW|]. exists regs', mem', md'.
    split; [exact Hc|]. split; [exact HAR'|]. split; [exact Hpr|]. split; [exact Hsm|].
    split; [exact (iff_trans HQ IFF)|]. split; [exact HK|]. split; [exact HP1 | exact HP2].
Qed.

(** ** The cut's facts back, after the call *)
Lemma a12_sc_after : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc memc' mdc' (rX' : bvmap 5 word),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) ->
     rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  pf_rg rX' (a5_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' PF_SC_LINE.
Proof.
  intros v pos lyc Sc Wc rX memc mdc memc' mdc' rX' HB HJ' HK HP HRG.
  destruct (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
  pose proof G as (_ & _ & _ & G4 & _).
  pose proof STK_values as (_ & _ & _ & SPF & _).
  (* the window [s1 - 2 ESTACK, s1) lies in a5_Wrx's first disjunct [sp0 - 12800, s1) *)
  assert (HK5 : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a -> rdW Wc memc' a = rdW Wc memc a).
  { intros sl shw a Ha Hw. apply HK; [exact Ha|]. intros Hwin. apply Hw. unfold a5_Wrx. left.
    rewrite SPF. unfold ESTACK in Hwin. lia. }
  pose proof HB as (_ & _ & _ & _ & HFSH).
  apply (a5_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc rX' memc' mdc' PF_SC_LINE HB HJ').
  - exists (st_fs Sc). apply a12c_set_fs_id.
  - apply Permutation_refl.
  - intros a Ha Hw. exact (HK5 true true a Ha Hw).
  - intros a Hv. exact (a12c_view_kept (w_H Wc) memc memc' a (HP a) Hv).
  - exact HRG.
  - exact (a5_keep_fsh v pos (rdW Wc memc) (rdW Wc memc') true PF_SC_LINE G (HK5 true false) HFSH).
Qed.

End e.
End f.
End d.
