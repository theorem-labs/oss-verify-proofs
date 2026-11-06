(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp0e6 AIcpnnp AIcpya4 AIcpw0i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_WSvfw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_WSvfw.

Module A_HKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_World A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_ImgLow OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEnv3.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.

  Definition app_ivl (iv : Z * Z) : Prop := exists p n, app_range LPA p n /\ p <= fst iv /\ snd iv <= p + n.
  Definition const_free_ivl3 (iv : Z * Z) : Prop := const_free_ivl2 iv \/ app_ivl iv.

  (* [comment removed for export] *)
  Lemma app_ivl_apart : forall lo hi a, app_ivl (lo, hi) ->
    (0x10000 <= a < 0x60a000 \/ 0x7fffa000 <= a < CONSTS_TOP2) -> ~ (lo <= a < hi).
  Proof.
    (intros lo hi a; (first [ intro dR_8; dex2 dR_8 as p n; dand3 dR_8 as AR P1 P2 | intro dR_8; dand5 dR_8 as p n AR P1 P2 | intros (p & n & AR & P1 & P2) ]); intros Ha). cbn [fst snd] in P1, P2.
    (first [ pose proof ((app_facts LPA p n AR)) as dR_1; dand4 dR_1 as _ IMG NS _ | pose proof (app_facts LPA p n AR) as (_ & IMG & NS & _) ]). unfold off_image in IMG. cbn [cl_image_lo cl_image_hi LPA] in IMG.
    unfold CONSTS_TOP2 in Ha. lia.
  Qed.

  Lemma const_free_outside3 : forall W a, Forall const_free_ivl3 W ->
    0x7fffa000 <= a < CONSTS_TOP2 -> outside W a.
  Proof.
    intros W a FW Ha. induction W as [|[lo hi] W IH]; [exact I|].
    cbn. apply Forall_cons_iff in FW as [F1 FW]. split; [| exact (IH FW)].
    destruct F1 as [F1|F1].
    - unfold const_free_ivl2, const_free_ivl, CONSTS_TOP, CONSTS_TOP2 in F1. cbn in F1. unfold CONSTS_TOP2 in Ha. lia.
    - apply (app_ivl_apart lo hi a F1). right. exact Ha.
  Qed.

  Lemma consts_hold_munch3 : forall W m m',
    consts_hold LPA m -> munch W m m' -> Forall const_free_ivl3 W -> consts_hold LPA m'.
  Proof.
    intros W m m' CH MU FW. unfold consts_hold in *. rewrite Forall_forall in CH |- *.
    pose proof consts_const_free2 as CF. rewrite Forall_forall in CF.
    intros c Hc. specialize (CH c Hc). (first [ pose proof ((CF c Hc)) as dR_2; dand3 dR_2 as C1 C2 C3 | destruct (CF c Hc) as (C1 & C2 & C3) ]).
    eapply bytes_at_munch; [exact CH| exact MU|].
    intros a Ha. clear CH Hc MU. induction W as [|[lo hi] W IH]; [exact I|].
    cbn. apply Forall_cons_iff in FW as [F1 FW]. split; [| exact (IH FW)].
    destruct F1 as [F1|F1].
    - unfold const_free_ivl2, const_free_ivl, CONSTS_TOP, CONSTS_TOP2 in F1. cbn in F1. unfold CONSTS_TOP2 in C3. lia.
    - apply (app_ivl_apart lo hi a F1). unfold CONSTS_TOP2 in *. lia.
  Qed.

  Lemma cenv_munch3 : forall W m m',
    cenv m -> munch W m m' -> Forall const_free_ivl3 W -> cenv m'.
  Proof.
    intros W m m' [CH VIS] MU FW. split; [eapply consts_hold_munch3; eauto|].
    intros a Ha NS. eapply mapped_munch; [exact MU| | | | exact (VIS a Ha NS)].
    - unfold sh, kShadowOffset. pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)).
      assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
    - unfold sh, kShadowOffset. pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)).
      assert (a / 8 <= 0x60a000 / 8) by (apply Z.div_le_mono; lia). change (0x60a000 / 8) with 791552 in *. lia.
    - intros i Hi. apply const_free_outside3; [exact FW|]. unfold sh, kShadowOffset, CONSTS_TOP2.
      pose proof (Z.div_mod (a / 8 + 2147450880) 8 ltac:(lia)) as DM.
      pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)).
      assert (0x10000 / 8 <= a / 8) by (apply Z.div_le_mono; lia).
      assert (a / 8 <= 0x609fff / 8) by (apply Z.div_le_mono; lia).
      change (0x10000 / 8) with 8192 in *. change (0x609fff / 8) with 791551 in *. lia.
  Qed.

  Lemma const_free_ivl3_of2 : forall iv, const_free_ivl2 iv -> const_free_ivl3 iv.
  Proof. intros iv H. left. exact H. Qed.
  Lemma const_free_ivl3_app : forall p n lo hi, app_range LPA p n -> p <= lo -> hi <= p + n -> const_free_ivl3 (lo, hi).
  Proof. intros p n lo hi AR H1 H2. right. exists p, n. cbn [fst snd]. split; [exact AR| split; [exact H1| exact H2]]. Qed.
  Lemma const_free_ivl3_frame_shadow : forall p n k, app_range LPA p n -> 0 <= k -> k <= (n + 7) / 8 -> const_free_ivl3 (sh p, sh p + k).
  Proof. intros p n k AR K0 K1. left. apply (app_shadow_const_free2 LPA p n k AR eq_refl eq_refl K0 K1). Qed.
  (* [comment removed for export] *)
  Lemma const_free_ivl3_high : forall lo hi, alloc_ceiling <= lo -> const_free_ivl3 (lo, hi).
  Proof.
    intros lo hi H. left. left. unfold const_free_ivl, CONSTS_TOP. cbn [fst snd]. left.
    pose proof (layout_facts (L:=LPA)) as LF. unfold kHighMemBeg in LF. pose proof alloc_ceiling_num as ACV. lia.
  Qed.
End CEnv3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame7.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.

  Lemma fsize7 : fsize HCLASS = 8192. Proof. reflexivity. Qed.

  Lemma smalloc7_acall :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs (aview A m) ->
      a0 = Z_to_bv 64 4320 ->
      (forall ff age, a_frame A ff = Some (HCLASS, age) -> Z.of_nat age + 2 < fslots HCLASS) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped (aview A m) (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (ff : Z) (A' : AS) (m' : mem) (md' : Model)
              (junk : list byte) (shj : list byte),
          ainv A' m' md' -> mem_inv rsegs (aview A' m') -> amd_frame md md' ->
          (forall q, a_live A' q = a_live A q) -> a_livebytes A' = a_livebytes A -> a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A (* [comment removed for export] *) ->
          ff <> 0 -> a_frame A ff = None -> a_frame A' ff = Some (HCLASS, 0%nat) ->
          (forall g k' age', g <> ff -> a_frame A g = Some (k', age') ->
              a_frame A' g = Some (k', if Z.eqb k' HCLASS then S age' else age')) ->
          (forall g, g <> ff -> a_frame A g = None -> a_frame A' g = None) ->
          (* [comment removed for export] *)
          ff mod 32 = 0 /\ app_range LPA ff 8192 /\ ff + 8192 <= alloc_ceiling /\ 0 <= sh ff /\ sh ff + 1024 <= SHMAX ->
          (* [comment removed for export] *)
          length junk = 8184%nat -> rw_cells rsegs (aview A' m') ff [CB 8184 junk] ->
          length shj = 1024%nat -> rw_cells rsegs (aview A' m') (sh ff) [CB 1024 shj] ->
          frame_ok LPA (owned A) (owned A') (bv_unsigned sp) ASTK nowhere (frm ff HCLASS) (aview A m) (aview A' m') ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 ff) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_smalloc_pc LPA HCLASS) fc None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AI0 MI Ha0 YOUNG TP SP16 RA2 CEIL MP KK.
    eapply (as_smalloc_cps LPA HCLASS); [exact AI0| exact MI| right; right; reflexivity
      | exact Ha0| rewrite fsize7; lia| intros _; reflexivity| exact YOUNG| exact TP| exact SP16| exact RA2| exact CEIL| exact MP|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A' m' md'. cbv zeta.
    intros AI' MI' MDF HH HE LV LB TC NL SC PC NZ FN FF AGE NONE AZ FR.   (* [comment removed for export] *)
    change (aview_of (ahull A') m') with (aview A' m') in MI', AZ, FR.
    change (aview_of (ahull A) m) with (aview A m) in FR.
    (first [ pose proof ((fframe_cells A' m' md' ff HCLASS 0%nat AI' FF)) as dR_3; dex1 dR_3 as junk; destruct dR_3 as [LJ FC] | pose proof ((fframe_cells A' m' md' ff HCLASS 0%nat AI' FF)) as dR_3; dand3 dR_3 as junk LJ FC | destruct (fframe_cells A' m' md' ff HCLASS 0%nat AI' FF) as (junk & LJ & FC) ]).
    (first [ pose proof ((fshadow_cells A' m' md' ff HCLASS 0%nat AI' FF)) as dR_4; dex1 dR_4 as shj; destruct dR_4 as [LS SC0] | pose proof ((fshadow_cells A' m' md' ff HCLASS 0%nat AI' FF)) as dR_4; dand3 dR_4 as shj LS SC0 | destruct (fshadow_cells A' m' md' ff HCLASS 0%nat AI' FF) as (shj & LS & SC0) ]).
    (first [ pose proof ((fframe_geom LPA A' m' md' ff HCLASS 0%nat AI' FF)) as dR_5; dand5 dR_5 as K0 FS LO HI _ | destruct (fframe_geom LPA A' m' md' ff HCLASS 0%nat AI' FF) as (K0 & FS & LO & HI & _) ]).
    (first [ pose proof ((as_frame_ok LPA A' m' md' ff HCLASS 0%nat AI' FF)) as dR_6; dand3 dR_6 as _ AL _ | destruct (as_frame_ok LPA A' m' md' ff HCLASS 0%nat AI' FF) as (_ & AL & _) ]).
    rewrite fsize7 in *. change (Z.to_nat (8192 - 8)) with 8184%nat in LJ, FC. change (Z.to_nat (8192 / 8)) with 1024%nat in LS, SC0.
    pose proof (app_facts LPA ff 8192 LO) as (FB & _).
    (first [ pose proof ((sh_bound ff 8192 ltac:(lia) ltac:(lia) HI)) as dR_7; dand3 dR_7 as S0 S1 _ | pose proof (sh_bound ff 8192 ltac:(lia) ltac:(lia) HI) as (S0 & S1 & _) ]).
    change ((8192 + 7) / 8) with 1024 in S1.
    eapply (KK t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A' m' md' junk shj);
      [ exact AI' | exact MI' | exact MDF | exact LV | exact LB | exact TC | exact NL | exact SC | exact PC | exact NZ | exact FN | exact FF | exact AGE | exact NONE
      | | exact LJ | exact FC | exact LS | exact SC0 | exact FR ].
    split; [| split; [exact LO| split; [exact HI| split; [exact S0| exact S1]]]].
    change (Z.min 8192 4096) with 4096 in AL.
    pose proof (Z.div_mod ff 4096 ltac:(lia)) as D. rewrite AL, Z.add_0_r in D. rewrite D.
    replace (4096 * (ff / 4096)) with ((128 * (ff / 4096)) * 32) by lia. apply Z_mod_mult.
  Qed.

  Lemma sfree7_acall :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (ff : Z) (age : nat) (T : TSet),
      ainv A m md -> mem_inv rsegs (aview A m) ->
      a0 = Z_to_bv 64 ff -> a1 = Z_to_bv 64 4320 ->
      a_frame A ff = Some (HCLASS, age) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped (aview A m) (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model),
          ainv (a_release A ff) m' md' -> mem_inv rsegs (aview (a_release A ff) m') -> amd_frame md md' ->
          frame_ok LPA (owned A) (owned (a_release A ff)) (bv_unsigned sp) ASTK (frm ff HCLASS) nowhere (aview A m) (aview (a_release A ff) m') ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_sfree_pc LPA HCLASS) fc None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. intros AI0 MI Ha0 Ha1 HF TP SP16 RA2 CEIL MP KK.
    eapply (as_sfree_cps LPA HCLASS); [exact AI0| exact MI| reflexivity| exact Ha0| exact Ha1| rewrite fsize7; lia| intros _; reflexivity
      | exact HF| exact TP| exact SP16| exact RA2| exact CEIL| exact MP|].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' md'. cbv zeta.
    intros AI' MI' MDF FR.
    change (aview_of (ahull (a_release A ff)) m') with (aview (a_release A ff) m') in MI', FR.
    change (aview_of (ahull A) m) with (aview A m) in FR.
    eapply KK; [exact AI'| exact MI'| exact MDF| exact FR].
  Qed.
End Frame7.
End A_HKit.


Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, memset_icpt_post,
  WSASSERT_STACK, WSEMU_STACK, MEMSET_ICPT_STACK, h_ws, h_wsbuf in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @ACV; @G2_03; @SPR; @CEIL; @G0; @Wlo; @IDL; @PADL; @P0; @PHI; @G3; @Vlo; @PLO; @NEwv; @DWV; @SZ; @SR; @G2_08; @G2_09; @H0; @G2_05; @Whi; @DJw; @Wlo_l; @DJv; @G2_06; @G2_07; @Vlo_l; @X; @K0; @V16K; @ESB; @G2_13; @Hx__; @V16C0; @Ha__; @G2_14; @SHvT; @LO0; @SHvN; @LZ; @ESW; @SHwT; @SBhi; @SHwaN; @Vhi; @SSP; @NO; @G2_11; @SHwaB; @SHBR; @W8; @W16; @SBlo; @LSW; @LSB; @GLE; @GGE; @GCE; @KS])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Lemma pa_site_10e5f8 : In 0x88820 (cl_sites LPA). Proof. cbn. tauto. Qed.
Lemma pa_site_10e3c0 : In 0x885e8 (cl_sites LPA). Proof. cbn. tauto. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma WS_Rollback_ok : WS_Rollback_stmt.
  Proof.
    unfold WS_Rollback_stmt, frames_same.
    intros H E lo SB N. intros until T. cbv zeta. intros AINV MI Ha0 Ha1 WSX GLOB HSH HFR TP SP16 ST CEIL LO SSH K.
    rewrite Ha0, Ha1. unfold WS_Rollback_entry, WSROLLBACK_STACK, WSRESET_STACK, WSAFREE_STACK, ASTK in *.
    pose proof alloc_ceiling_num as ACV.
    pose proof (henv_geom_of_frame LPA A m md H AINV HFR) as HG.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3. all_app_facts. (* [comment removed for export] *) pose proof G2 as G2x__; dand17 G2x__ as G2_01 G2_02 G2_03 G2_04 G2_05 G2_06 G2_07 G2_08 G2_09 G2_10 G2_11 G2_12 G2_13 G2_14 G2_15 G2_16 G2_17. hide G2.
    pose proof (hff_al8 H 2976 HG eq_refl) as AL1. pose proof (hff_al8 H 3152 HG eq_refl) as AL2. pose proof (hff_al8 H 1536 HG eq_refl) as AL3.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHFR.
    change ((8192 + 7) / 8) with 1024 in SHFR. rewrite SHMAX_val in SHFR.
    assert (ESW : sh (h_ff H + 2976) = sh (h_ff H) + 372) by (unfold sh; mlia).
    assert (ESB : sh (h_ff H + 3152) = sh (h_ff H) + 394) by (unfold sh; mlia).
    assert (LSW : Z.of_nat (length (shpat 40)) = 5) by reflexivity.
    assert (LSB : Z.of_nat (length (shpat 1024)) = 128) by reflexivity.
    pose proof HFR as [age HFR'].
    (* [comment removed for export] *)
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. fold_aview. open_map_cells MC.
    pose proof (got_cp_cell _ (proj1 CE)) as GOTC. unfold GOTA_cp in GOTC. cbn [vi_bss_cp VIA] in GOTC. fold_aview.
    (first [ pose proof (HSH) as dR_2; dand10 dR_2 as _ SHC _ _ _ _ SHW _ _ SHB | pose proof HSH as (_ & SHC & _ & _ & _ & _ & SHW & _ & _ & SHB) ]). fold_cl_segs. fold_aview. unfold h_ws, h_wsbuf, h_cp in SHC, SHW, SHB.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2976) 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHWR. rewrite SHMAX_val in SHWR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 3152) 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as SHBR. rewrite SHMAX_val in SHBR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 1536) 752 ltac:(lia) ltac:(lia) ltac:(lia)) as SHCR. rewrite SHMAX_val in SHCR.
    (first [ pose proof ((shadowed_bss_cp _ (proj1 CE))) as dR_3; dand8 dR_3 as PG NG SHG GAL G0 GLE GGE GCE | destruct (shadowed_bss_cp _ (proj1 CE)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE) ]). fold_cl_segs. fold_aview.
    cbn [vi_bss_cp VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_4; dand4 dR_4 as _ BSS CP _ | pose proof GLOB as (_ & BSS & CP & _) ]). fold_cl_segs. fold_aview. cbn [vi_bss_cp VIA] in BSS. unfold h_cp in BSS, CP.
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp); (h_ff H + 2976, h_ff H + 2976 + 40); (h_ff H + 3152, h_ff H + 3152 + 32)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WMAP : mapped (aview A m) (bv_unsigned sp - 8320) 8320).
    { eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8320, bv_unsigned sp); (h_ff H + 2976, h_ff H + 2976 + 40); (h_ff H + 3152, h_ff H + 3152 + 32)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8320)) with 8320 by lia; exact WMAP |].
      split; [right; right; left; exists (h_ff H), HCLASS, age; split; [exact HFR'|]; change (fsize HCLASS) with 8192; lia|].
      split; [| exact I]. right. right. left. exists (h_ff H), HCLASS, age. split; [exact HFR'|]. change (fsize HCLASS) with 8192. lia. }
    unfold h_ws, h_wsbuf, h_cp in *.
    assert (WS0P : forall mq idq, ws_id_ok idq ->
      rw_cells rsegs mq (h_ff H + 2976) [C4 (Z_to_bv 64 WS_MAGIC); CB 4 idq; C8 (Z_to_bv 64 (h_ff H + 3152)); C8 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_ff H + 3152 + 1016))] ->
      rw_cells rsegs mq (h_ff H + 3152) [C4 (Z_to_bv 64 WS_EMU_MAGIC); C4 (Z_to_bv 64 1016); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 (h_ff H + 3152 + 16))] ->
      ws0_obj LPA H mq).
    { intros mq idq IDq X1 X2. apply (ws0_obj_intro LPA H mq idq IDq); [exact X1| exact X2]. }
    destruct E as [[wa vep]|].
    - (* [comment removed for export] *)
      (first [ pose proof (WSX) as dR_5; dex2 dR_5 as id pad; dand7 dR_5 as IDOK PADL WSC WEC LIVEwa WAC LIVEvep | pose proof (WSX) as dR_5; dand9 dR_5 as id pad IDOK PADL WSC WEC LIVEwa WAC LIVEvep | pose proof WSX as (id & pad & IDOK & PADL & WSC & WEC & LIVEwa & WAC & LIVEvep) ]). fold_cl_segs. fold_aview.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      assert (ID0 : exists b0, id = b0 :: [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0] /\ Z.lor (bv_unsigned b0) 32 = 114).
      { destruct IDOK as [-> | ->]; eexists; (split; [reflexivity| reflexivity]). }
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS1 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC.
      unfold h_ws, h_wsbuf in WSC, WEC, WAC.
      (first [ pose proof ((live_geomP LPA A m md wa _ AINV LIVEwa)) as dR_6; dand7 dR_6 as _ W16 Wlo Whi _ _ _ | pose proof (live_geomP LPA A m md wa _ AINV LIVEwa) as (_ & W16 & Wlo & Whi & _ & _ & _) ]).
      (first [ pose proof ((live_geomP LPA A m md vep _ AINV LIVEvep)) as dR_7; dand7 dR_7 as _ V16 Vlo Vhi _ _ _ | pose proof (live_geomP LPA A m md vep _ AINV LIVEvep) as (_ & V16 & Vlo & Vhi & _ & _ & _) ]).
      unfold kHighMemBeg in Wlo, Vlo. all_app_facts. pose proof (mod8_of_mod16 wa W16) as W8.
      assert (NEwv : wa <> vep) by (intros ->; rewrite LIVEvep in LIVEwa; discriminate).
      pose proof (as_live_disjoint LPA A m md wa 40 vep 312 AINV LIVEwa LIVEvep NEwv) as DWV.
      pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS age wa 40 AINV HFR' LIVEwa) as DJw.
      pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS age vep 312 AINV HFR' LIVEvep) as DJv.
      change (fsize HCLASS) with 8192 in DJw, DJv.
      pose proof (as_live_shadow LPA A m md wa 40 AINV LIVEwa) as SHwa. fold_cl_segs. fold_aview.
      pose proof (shpat_sh_boundL (Clg:=Clg) wa 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwaB. rewrite SHMAX_val in SHwaB.
      pose proof (sh_boundL (Clg:=Clg) wa 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwaN. rewrite SHMAX_val in SHwaN.
      pose proof (sh_boundL (Clg:=Clg) vep 312 ltac:(lia) ltac:(lia) ltac:(lia)) as SHvN. rewrite SHMAX_val in SHvN.
      (* [comment removed for export] *)
      pose proof (sh_le_ceiling vep 312 (mod8_of_mod16 vep V16) ltac:(lia) Vhi) as SHvT.
      pose proof (sh_le_ceiling wa 40 W8 ltac:(lia) Whi) as SHwT.
      (* [comment removed for export] *)
      (first [ pose proof ((stack_shadow_open (Clg:=Clg) _ _ _ _ _ SSH ltac:(lia))) as dR_8; dand12 dR_8 as P zs SS Ezs LZ ESP P8 P0 PLO PHI SBlo SBhi | destruct (stack_shadow_open (Clg:=Clg) _ _ _ _ _ SSH ltac:(lia)) as (P & zs & SS & Ezs & LZ & ESP & P8 & P0 & PLO & PHI & SBlo & SBhi) ]).
      fold_aview. try rewrite SHMAX_val in SBlo. unfold kHighMemBeg in SBhi. all_app_facts. pose proof (stack_shadow_pure _ _ _ _ _ SSH) as SSP.
      ago AINV. fold_cl_segs.
      carve_frame 32%nat ST.
      do 5 zstep.
      (* [comment removed for export] *)
      do 6 zstep.
      icall (WS_Assert_ok H (Some (A, wa, vep)) lo) by
        (first [ (hnf; split; [ eapply (ws1_obj_intro LPA H A _ wa vep id pad IDOK PADL); [exact WSC| exact WEC| exact LIVEwa| exact WAC| exact LIVEvep] |];
                  split; [exists wa, 40; split; [exact SHwa| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia]|]; unfold kHighMemBeg; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia)
               | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. first [if_true | if_false].
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep.
      (* [comment removed for export] *)
      shadow_chk SHW 4 11. zstep. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk SHW 1 12.
      (first [ dex1 ID0 as b0; destruct ID0 as [-> E114] | dand3 ID0 as b0 -> E114 | destruct ID0 as (b0 & -> & E114) ]).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (rw_cells_split_CB rsegs mx (h_ff H + 2976) [C4 (Z_to_bv 64 WS_MAGIC)] 4 (b0 :: [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0])
                    [C8 (Z_to_bv 64 (h_ff H + 3152)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_ff H + 3152 + 1016))]
                    [1; 3]%nat WSC eq_refl) as WSC1 end.
      clear WSC. cbn [mk_CB_cells firstn skipn app] in WSC1.
      zstep. zstep. rewrite E114. zstep. fix_bstore; mem_after_store.
      lazymatch type of WSC1 with rw_cells _ ?mx ?b (?c0 :: ?c1 :: ?c2 :: ?rest) =>
        pose proof (rw_cells_merge rsegs mx b [c0] [c1; c2] rest WSC1) as WSC end.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in WSC. clear WSC1.
      (* [comment removed for export] *)
      do 7 zstep.
      try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      zstep.
      (* [comment removed for export] *)
      carve_frame 64%nat ST.
      do 8 zstep.
      (* [comment removed for export] *)
      do 6 zstep.
      icall (WS_Assert_ok H (Some (A, wa, vep)) lo) by
        (first [ (hnf; split; [ eapply (ws1_obj_intro LPA H A _ wa vep ws_id_req pad (or_introl eq_refl) PADL);
                                [exact WSC| exact WEC| exact LIVEwa| exact WAC| exact LIVEvep] |];
                  split; [exists wa, 40; split; [exact SHwa| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia]|]; unfold kHighMemBeg; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia)
               | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. kdead. zstep. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      shadow_addr_at SHG 6191712 8.
      match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
        let e' := eval vm_compute in e in change e with e' in RD end.
      zstep. zstep; if_cases K0; zify_cond K0;
        [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk SHC 1 12. zstep. (* [comment removed for export] *) match goal with |- context [ zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn ?zk (repeat (Z_to_bv 8 0) ?zn))))) ] => replace (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn zk (repeat (Z_to_bv 8 0) zn)))))) with (Z_to_bv 64 0) by (vm_compute; reflexivity) end. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. zstep.
      icall (ws_emu_ok H (ws_rec_of H ws_id_req) (wsemu_WS1 wa) lo)
        by (first [ exact WSC | exact WEC | reflexivity | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk0 SHB 8. zstep.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHwa 8. zstep. shadow_chk0 SHB 8.
      (* [comment removed for export] *)
      zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHwa 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      rename FR into FRr. carve_frame 32%nat ST.
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      pose proof SS as SSX. rewrite Ezs, <- ESP in SSX.
      shadow_chk0z SSX 8. clear SSX.
      (* [comment removed for export] *)
      zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      shadow_chk SHwa 4 12. zstep. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHwa 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHwa 8. zstep. shadow_chk0 SHB 8.
      (* [comment removed for export] *)
      zstep. zstep.
      (* [comment removed for export] *)
      shadow_chk0 SHB 8. zstep.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHwa 8. zstep. zstep.
      (* [comment removed for export] *)
      astop AINV MU WM CFP. fold_cl_segs.
      pose proof (as_minv LPA A _ _ AINV) as [_ MH]. pose proof (as_minv LPA A _ _ AINV0) as [_ MH0].
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        assert (GLOB0 : glob_ok LPA VIA H (aview A mx)) by
         (eapply glob_ok_munch; [exact GLOB| exact MU| exact WM|];
          intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia);
        assert (HSH0 : hshadow LPA H (aview A mx)) by
         (eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia]);
        pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A mx) (bv_unsigned sp - 96) 32 AINV0 ltac:(lia) ltac:(lia)
                      (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CRF2;
        pose proof (crange_block (Clg:=Clg) (L:=LPA) A _ _ wa 40 wa 40 AINV0 LIVEwa ltac:(lia) ltac:(lia) ltac:(lia)) as CRwa;
        pose proof (crange_sshadow (Clg:=Clg) A _ _ SB N zs AINV0 SS LZ ltac:(try rewrite SHMAX_val; lia) ltac:(unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; lia)) as CRSS
      end.
      ws_cranges H AINV0 HFR' FRr.
      eapply (as_free_cps LPA) with (p := vep) (n0 := 312);
        [ exact AINV0 | assumption | reflexivity | right; exact LIVEvep | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; apply pa_site_10e5f8
        | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; unfold ASTK; lia
        | rewrite unsigned_lit by lia; unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL | lia | lia]
        | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md2. cbv zeta.
      intros AINV1 MI1 MDF1 _ FRS1 DEAD1 LIVEq1 LBY1 TCR1 SCR1 PCR1 NL1 ERRNO1 FRK1.   (* [comment removed for export] *)
      fold_cl_segs. fold_aview. rewrite unsigned_lit in FRK1 by lia. unfold ASTK in FRK1.
      assert (HFR1 : hframe LPA A1 H) by (eapply hframe_keep; [exact HFR| exact FRS1]). pose proof HFR1 as [age1 HFR1'].
      assert (GLOB1 : glob_ok LPA VIA H (aview A1 m2)).
      { eapply glob_ok_acall_blk; [exact AINV0| exact HFR| apply (cframe_of_frame_ok LPA); exact FRK1| exact GLOB0| lia| exact LIVEvep]. }
      assert (HSH1 : hshadow LPA H (aview A1 m2)).
      { eapply hshadow_acall_blk; [exact AINV0| exact HFR| apply (cframe_of_frame_ok LPA); exact FRK1| exact HSH0| lia| exact LIVEvep]. }
      pose proof (cenv_intro A1 m2 md2 AINV1) as CE1.
      assert (LIVEwa1 : a_live A1 wa = Some 40) by (rewrite (LIVEq1 wa NEwv); exact LIVEwa).
      acall_xfer FRK1.
      pose proof (as_live_shadow LPA A1 m2 md2 wa 40 AINV1 LIVEwa1) as SHwa1. fold_cl_segs. fold_aview.
      pose proof (live_range_ok (Clg:=Clg) A1 m2 md2 wa 40 wa 4 AINV1 LIVEwa1 ltac:(lia) ltac:(lia) ltac:(lia)) as RWwa.
      pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp); (wa, wa + 40)] (aview A1 m2)) as MU2.
      pose proof (wmono_refl rsegs (aview A1 m2)) as WM2.
      assert (WMAP2 : mapped (aview A1 m2) (bv_unsigned sp - 8320) 8320).
      { lazymatch type of FR with rw_cells _ _ _ ?cs1 => lazymatch type of FRr with rw_cells _ _ _ ?cs2 =>
          assert (FRboth : rw_cells rsegs (aview A1 m2) (bv_unsigned sp + -96) (cs1 ++ cs2))
            by (apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR|];
                cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -96 + Z.of_nat 32) with (bv_unsigned sp + -64) by lia; exact FRr)
        end end.
        eapply (window_mapped LPA _ lo); [exact ST | exact FRboth | cbn [cells_size csize Nat.add app]; lia | exact CEIL | lia | lia]. }
      assert (CFP2 : client_fp LPA A1 (aview A1 m2) [(bv_unsigned sp - 8320, bv_unsigned sp); (wa, wa + 40)]).
      { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8320)) with 8320 by lia; exact WMAP2 |].
        split; [right; left; exists wa, 40; split; [exact LIVEwa1|lia]| exact I]. }
      pose proof (map_cells_of_consts _ (proj1 CE1)) as MC1. fold_aview. open_map_cells MC1.
      pose proof (got_memset_cell _ (proj1 CE1)) as GMS. unfold GOTA_memset, MEMSET_ICPT_ENTRY in GMS. fold_aview.
      (first [ pose proof ((asan_memset_cells_of_consts _ (proj1 CE1))) as dR_10; dand4 dR_10 as Gric Cric Crms _ | destruct (asan_memset_cells_of_consts _ (proj1 CE1)) as (Gric & Cric & Crms & _) ]). fold_aview.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      do 8 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with X : rw_cells rsegs mx wa (?c0 :: ?rest) |- _ =>
          pose proof (proj1 (rw_cells_app rsegs mx wa [c0] rest) X) as [NBa NBb]; clear X;
          destruct (rw_cells_forget _ _ _ _ NBa) as [junkm NBm]; clear NBa; cbn [cells_size csize Nat.add] in NBm, NBb end end.
      icall memset_icpt_spec by
        (rewrite ?unsigned_lit by lia;
         first [ exact NBm | exact ST | exact CEIL | rebundle
               | (unfold MEMSET_ICPT_STACK; lia)
               | (left; lia)
               | lia
               | (right; eapply range_ok_high_munch; [exact RWwa| exact MU2| lia| lia| lia| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia])
               | assumption ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp + -64).
      zstep.
      (* [comment removed for export] *)
      astop AINV1 MU2 WM2 CFP2. fold_cl_segs.
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        assert (GLOB2 : glob_ok LPA VIA H (aview A1 mx)) by
         (eapply glob_ok_munch; [exact GLOB1| exact MU2| exact WM2|];
          intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia);
        assert (HSH2 : hshadow LPA H (aview A1 mx)) by
         (eapply hshadow_munch; [exact HSH1| exact MU2| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia]);
        pose proof (crange_sshadow (Clg:=Clg) A1 _ _ SB N zs AINV2 SS LZ ltac:(try rewrite SHMAX_val; lia) ltac:(unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; lia)) as CRSS2;
        (* [comment removed for export] *)
        assert (CFa : cframe LPA (owned A) (owned A1) (bv_unsigned sp) 8320
                        (fun a => (h_ff H + 2976 <= a < h_ff H + 2976 + 40 \/ h_ff H + 3152 <= a < h_ff H + 3152 + 32)
                                  \/ (newblk wa 40 a \/ newblk vep 312 a)) nowhere (aview A m) (aview A1 mx))
          by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A1 m2) _ _ _);
              [ exact MU | | exact FRK1 | lia | lia | intros a X; right; right; exact X | intros a X; destruct X
              | exact MU2 | | eapply (window_mapped LPA _ lo); [exact ST | exact FRr | cbn; lia | exact CEIL | lia | lia] ];
              intros a Ha NO; cbn [outside] in NO; unfold newblk, blk; clear - Wlo NO; lia)   (* [comment removed for export] *)
      end.
      ws_cranges H AINV2 HFR1' FRr.
      pose proof (as_minv LPA A1 _ _ AINV2) as [_ MH2].
      eapply (as_free_cps LPA) with (p := wa) (n0 := 40);
        [ exact AINV2 | assumption | reflexivity | right; exact LIVEwa1 | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; apply pa_site_10e3c0
        | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; unfold ASTK; lia
        | rewrite unsigned_lit by lia; unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL | lia | lia]
        | ].
      clear MU WM CFP FRK1 MU2 WM2 CFP2 GLOB0 HSH0.
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A2 m4 md4. cbv zeta.
      intros AINV3 MI3 MDF3 _ FRS3 DEAD3 LIVEq3 LBY3 TCR3 SCR3 PCR3 NL3 ERRNO3 FRK3.   (* [comment removed for export] *)
      fold_cl_segs. fold_aview. rewrite unsigned_lit in FRK3 by lia. unfold ASTK in FRK3.
      assert (HFR3 : hframe LPA A2 H) by (eapply hframe_keep; [exact HFR1| exact FRS3]). pose proof HFR3 as [age3 HFR3'].
      assert (GLOB3 : glob_ok LPA VIA H (aview A2 m4)).
      { eapply glob_ok_acall_blk; [exact AINV2| exact HFR1| apply (cframe_of_frame_ok LPA); exact FRK3| exact GLOB2| lia| exact LIVEwa1]. }
      assert (HSH3 : hshadow LPA H (aview A2 m4)).
      { eapply hshadow_acall_blk; [exact AINV2| exact HFR1| apply (cframe_of_frame_ok LPA); exact FRK3| exact HSH2| lia| exact LIVEwa1]. }
      pose proof (cenv_intro A2 m4 md4 AINV3) as CE3.
      acall_xfer FRK3.
      (first [ pose proof (HSH3) as dR_11; dand10 dR_11 as _ _ _ _ _ _ SHW3 _ _ SHB3 | pose proof HSH3 as (_ & _ & _ & _ & _ & _ & SHW3 & _ & _ & SHB3) ]). fold_cl_segs. fold_aview. unfold h_ws, h_wsbuf in SHW3, SHB3.
      pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp)] (aview A2 m4)) as MU3.
      pose proof (wmono_refl rsegs (aview A2 m4)) as WM3.
      assert (WMAP3 : mapped (aview A2 m4) (bv_unsigned sp - 8320) 8320).
      { eapply (window_mapped LPA _ lo); [exact ST | exact FRr | cbn; lia | exact CEIL | lia | lia]. }
      assert (CFP3 : client_fp LPA A2 (aview A2 m4) [(bv_unsigned sp - 8320, bv_unsigned sp)]).
      { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8320)) with 8320 by lia; exact WMAP3 | exact I]. }
      pose proof (map_cells_of_consts _ (proj1 CE3)) as MC3. fold_aview. open_map_cells MC3.
      ago AINV3. fold_cl_segs.
      (* [comment removed for export] *)
      shadow_rechk0 SHB3 (h_ff H + 3176) 8.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk0 SHB3 8. zstep. shadow_chk0 SHB3 8.
      (* [comment removed for export] *)
      zstep. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW3 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      do 9 zstep.
      try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FRr ST (bv_unsigned sp).
      zstep.
      lazymatch goal with X : rw_cells rsegs ?mx (h_ff H + 3152) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        replace (h_ff H + 3168) with (h_ff H + 3152 + 16) in X by lia end.
      icall (WS_Assert_ok H None lo) by (first [ (hnf; apply (WS0P _ ws_id_req (or_introl eq_refl)); assumption) | henv_side GLOB3 HSH3 HG CE3 MU3 WM3 ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      astop AINV3 MU3 WM3 CFP3.
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 mx mdx) end;
        [ assumption | assumption
        | eapply amd_frame_sbm_l; [exact SBM | exact MH |];
          eapply amd_frame_trans; [exact MDF1|]; eapply amd_frame_sbm_l; [exact SBM0 | exact (proj2 (as_minv LPA A1 _ _ AINV1)) |];
          eapply amd_frame_sbm_r; [exact MDF3 | eassumption]
        | intros ff; rewrite FRS3; apply FRS1 | rewrite TCR3, TCR1; reflexivity | rewrite SCR3, SCR1; reflexivity | rewrite PCR3, PCR1; reflexivity (* [comment removed for export] *) | exact ST
        | eapply glob_ok_munch; [exact GLOB3| exact MU3| exact WM3|
            intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia]
        | eapply hshadow_munch; [exact HSH3| exact MU3| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia]
        | apply (WS0P _ ws_id_req (or_introl eq_refl)); assumption
        | | ].
      { split; [exact DEAD3|]. split; [rewrite (LIVEq3 vep ltac:(intros E; exact (NEwv (eq_sym E)))); exact DEAD1|].
        split; [intros q Q1 Q2; rewrite (LIVEq3 q Q1); apply LIVEq1, Q2|]. split; [rewrite LBY3, LBY1; lia|].
        rewrite NL3, NL1. replace (vep =? 0) with false by (symmetry; apply Z.eqb_neq; try (generalize alloc_ceiling_val); clear - Vlo; try pose proof alloc_ceiling_val as ACV__; lia).
        replace (wa =? 0) with false by (symmetry; apply Z.eqb_neq; try (generalize alloc_ceiling_val); clear - Wlo; try pose proof alloc_ceiling_val as ACV__; lia). lia. }
      lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
        lazymatch type of CFa with cframe _ _ _ _ _ _ _ _ (aview A1 ?mp) =>
        assert (CFb : cframe LPA (owned A1) (owned A2) (bv_unsigned sp) 8320
                        (fun a => (h_ff H + 2976 <= a < h_ff H + 2976 + 40 \/ h_ff H + 3152 <= a < h_ff H + 3152 + 32)
                                  \/ (newblk wa 40 a \/ newblk vep 312 a)) nowhere (aview A1 mp) vfin)
          by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A1 mp) (aview A1 mp) (aview A2 m4) _ [] _);
              [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK3 | lia | lia
              | intros a X; right; left; exact X | intros a X; destruct X | exact MU3 |
              | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ];
              intros a Ha NO; cbn [outside] in NO; lia);
        eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m) (aview A1 mp) vfin CFa CFb); [lia | lia
            | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]
            | intros a [[X|X]|X]; [left; exact X| right; left; exact X| right; right; exact X]
            | intros a [[X|X]|X]; right; [left; exact X| right; left; exact X| right; right; exact X]
            | intros a X; destruct X ]
      end end.
    - (* [comment removed for export] *)
      (first [ pose proof (WSX) as dR_12; dex1 dR_12 as id; dand3 dR_12 as IDOK WSC WEC | pose proof (WSX) as dR_12; dand4 dR_12 as id IDOK WSC WEC | pose proof WSX as (id & IDOK & WSC & WEC) ]). fold_cl_segs. fold_aview.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      (* [comment removed for export] *)
      assert (ID0 : exists b0, id = b0 :: [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0] /\ Z.lor (bv_unsigned b0) 32 = 114).
      { destruct IDOK as [-> | ->]; eexists; (split; [reflexivity| reflexivity]). }
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      unfold h_ws, h_wsbuf in WSC, WEC.
      ago AINV. fold_cl_segs.
      carve_frame 32%nat ST.
      do 5 zstep.
      (* [comment removed for export] *)
      do 6 zstep.
      icall (WS_Assert_ok H None lo) by (first [ (hnf; apply (WS0P _ id IDOK); assumption) | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. first [if_true | if_false].
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep.
      (* [comment removed for export] *)
      shadow_chk SHW 4 11. zstep. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk SHW 1 12.
      (* [comment removed for export] *)
      (first [ dex1 ID0 as b0; destruct ID0 as [-> E114] | dand3 ID0 as b0 -> E114 | destruct ID0 as (b0 & -> & E114) ]).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (rw_cells_split_CB rsegs mx (h_ff H + 2976) [C4 (Z_to_bv 64 WS_MAGIC)] 4 (b0 :: [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0])
                    [C8 (Z_to_bv 64 (h_ff H + 3152)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_ff H + 3152 + 1016))]
                    [1; 3]%nat WSC eq_refl) as WSC1 end.
      clear WSC. cbn [mk_CB_cells firstn skipn app] in WSC1.
      zstep. zstep. rewrite E114. zstep. fix_bstore; mem_after_store.
      lazymatch type of WSC1 with rw_cells _ ?mx ?b (?c0 :: ?c1 :: ?c2 :: ?rest) =>
        pose proof (rw_cells_merge rsegs mx b [c0] [c1; c2] rest WSC1) as WSC end.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in WSC. clear WSC1.
      (* [comment removed for export] *)
      do 7 zstep.
      try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      zstep.
      (* [comment removed for export] *)
      carve_frame 64%nat ST.
      do 8 zstep.
      (* [comment removed for export] *)
      do 6 zstep.
      icall (WS_Assert_ok H None lo) by (first [ (hnf; apply (WS0P _ ws_id_req (or_introl eq_refl)); assumption) | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. kdead. zstep. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      shadow_addr_at SHG 6191712 8.
      match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
        let e' := eval vm_compute in e in change e with e' in RD end.
      zstep. zstep; if_cases K0; zify_cond K0;
        [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk SHC 1 12. zstep. (* [comment removed for export] *) match goal with |- context [ zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn ?zk (repeat (Z_to_bv 8 0) ?zn))))) ] => replace (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn zk (repeat (Z_to_bv 8 0) zn)))))) with (Z_to_bv 64 0) by (vm_compute; reflexivity) end. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. zstep.
      icall (ws_emu_ok H (ws_rec_of H ws_id_req) (wsemu_WS0 (h_ff H + 3152)) lo)
        by (first [ exact WSC | exact WEC | reflexivity | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk0 SHB 8. zstep.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHB 8. zstep. shadow_chk0 SHB 8.
      (* [comment removed for export] *)
      zstep. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      do 9 zstep.
      try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      zstep.
      icall (WS_Assert_ok H None lo) by (first [ (hnf; apply (WS0P _ ws_id_req (or_introl eq_refl)); assumption) | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      astop AINV MU WM CFP.
      pose proof (as_minv LPA A _ _ AINV) as [_ MH]. pose proof (as_minv LPA A _ _ AINV0) as [_ MH0].
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mx mdx) end;
        [ assumption | assumption
        | eapply amd_frame_sbm_l; [exact SBM | exact MH | apply amd_frame_refl; exact MH0]
        | intros ff; reflexivity | reflexivity | reflexivity | reflexivity (* [comment removed for export] *) | exact ST
        | eapply glob_ok_munch; [exact GLOB| exact MU| exact WM|
            intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia]
        | eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia]
        | apply (WS0P _ ws_id_req (or_introl eq_refl)); assumption
        | split; [intros p; reflexivity| split; reflexivity]
        | ].
      eapply cframe_stores; [exact MU| | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]].
      intros a Ha NO. cbn [outside] in NO. unfold h_ws, h_wsbuf. lia.
  Qed.
End S.
