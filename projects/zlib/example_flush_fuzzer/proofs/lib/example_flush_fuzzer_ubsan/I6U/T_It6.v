(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
(* reloc-zl14tag tagged blocks: agree 4 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK Require Import ZTac ZMem ZCall ZCallL ZArr ZArr4. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK6 Require Import IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6S Require Import S_It0 S_It3 S_It4 S_It6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6U Require Import Base T_It1 T_It2 T_It3 T_It4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section U7IT6.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation PR6 := (pregs6_t ty lens_ofs p pb sp vgp vtp).
#[local] Abbreviation PR8 := (pregs8 ty lens_ofs p pb sp vgp vtp).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregs_t ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs_t p).
#[local] Abbreviation CM := (cmem_t ty lf lens_ofs codes nx bits wf p sp).
#[local] Abbreviation SM := (smem_t p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).
#[local] Abbreviation st0 := (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).
#[local] Abbreviation C192' := (C192 ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C).

Definition rsT : list (Z * Z) := [(p + 1368, 5776); (p + 144, 8); (pb, 4)].
Ltac xaddr_t := pose proof (xaddr_facts_t _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN & XAE & XBE).
Ltac close_pregs6_t := unfold pregs6_t; split_conj; zreg.
Ltac open_pregs6_t H := unfold pregs6_t in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in destruct H as (a & b & c & d & e & g & h & i).

Definition slots_t (M : mem) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : Z) : Prop :=
  mem_u64 R_segs M (sp + -8) v1 /\ mem_u64 R_segs M (sp + -16) v8 /\ mem_u64 R_segs M (sp + -24) v9 /\
  mem_u64 R_segs M (sp + -32) v18 /\ mem_u64 R_segs M (sp + -40) v19 /\ mem_u64 R_segs M (sp + -48) v20 /\
  mem_u64 R_segs M (sp + -56) v21 /\ mem_u64 R_segs M (sp + -64) v22 /\ mem_u64 R_segs M (sp + -72) v23 /\
  mem_u64 R_segs M (sp + -80) v24 /\ mem_u64 R_segs M (sp + -88) v25 /\ mem_u64 R_segs M (sp + -96) v26 /\
  mem_u64 R_segs M (sp + -104) v27.

Definition pregs3_t (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -208 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp.
Ltac close_pregs3_t := unfold pregs3_t; split_conj; zreg.

Lemma init_t : forall Rb l M MD T,
  m_halted MD = None -> PR8 Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  zget_l Rb l kT2 = it_match ty -> zget_l Rb l kA6 = 1 -> zget_l Rb l kS2 = p + 1368 + 4 * nx ->
  1 <= mx ->
  mem_wr R_segs M (sp - 208) 208 -> mem_wr R_segs M p 7160 ->
  mem_arr 2 R_segs M (p + 152) 320 lf -> mem_arr 2 R_segs M (p + 792) 288 (arr_get work1Ar) ->
  mem_u64 R_segs M (p + 144) (p + 1368 + 4 * nx) ->
  mem_u64 R_segs M (sp + -208) (EXA ty p) -> mem_u64 R_segs M (sp + -192) (BSA ty p) -> mem_u64 R_segs M (sp + -184) (isL ty + isD ty) ->
  mem_arr 2 R_segs M (EXM ty p) (NE ty) (it_extra ty work1Ar) -> mem_arr 2 R_segs M (BSM ty p) (NE ty) (it_base ty work1Ar) ->
  SM st0 M ->
  (forall R' M', CR R' [] -> SR st0 R' [] -> zget_l R' [] kT1 = t_len st0 - t_drop st0 -> zget_l R' [] kA2 = p + 792 + 2 * t_sym st0 ->
     mpost R_segs M M' (sp + -208) (sp + -168) 0 0 -> CM M' -> SM st0 M' ->
     realizes R_segs (zcfg R_segs 139704 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 139604 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 LA2 LA6 LS1 Hmx Wf Wp Hlens Hwork Hnext Hsl0 Hsl16 Hsl24 Hext Hbase HSM K.
  pose proof C as C'. open_itc C'. open_pregs8 HP. open_smem_t HSM. zkeys. xaddr_t. clear Hprom HtyC HtyD Hpb.
  cbn [t_count t_tbl itm_st0] in Hcnt, Htbl.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3). pose proof (pow2_le15 rt ltac:(lia)) as PRT.
  pose proof (mpost_stable R_segs M (sp + -208) (sp + -168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -208) (sp + -168) 0 0) M) by (apply mpost_refl).
  zrebase.
  zbr Rfd false.
  zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd. zsetreg (2 ^ rt) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd.
  zstep Rfd. znot.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ rt - 1) ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd.
  zstep Rfd. znot.
  zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
  - close_cregs_t.
  - unfold sregs_t. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low itm_st0]. rewrite itm_used_pow2 by lia.
    unfold lowS. cbn [Z.eqb Pos.eqb]. split_conj; zreg.
  - cbn [t_len t_drop itm_st0]. zreg.
  - cbn [t_sym itm_st0]. zreg.
  - exact HAG.
  - unfold cmem_t. split_conj; assumption.
  - unfold smem_t. cbn [t_count t_tbl itm_st0]. split; assumption.
Qed.

Lemma ty_cases_t :
  (ty = CODES /\ cty ty = 0 /\ it_match ty = 20 /\ EXA ty p = 0 /\ BSA ty p = 0 /\ NE ty = 288 /\ isL ty = 0 /\ isD ty = 0)
  \/ (ty = LENS /\ cty ty = 1 /\ it_match ty = 257 /\ EXA ty p = 75248 /\ BSA ty p = 75186 /\ NE ty = 31 /\ isL ty = 1 /\ isD ty = 0)
  \/ (ty = DISTS /\ cty ty = 2 /\ it_match ty = 0 /\ EXA ty p = 75374 /\ BSA ty p = 75310 /\ NE ty = 32 /\ isL ty = 0 /\ isD ty = 1).
Proof using C zc ret sp pb wf cf bits nx codes lens_ofs lf. destruct ty; [left | right; left | right; right]; repeat split; reflexivity. Qed.

Lemma p144_al : (p + 144) mod 2 ^ 3 = 0.
Proof using C zc ret sp pb wf cf bits nx codes lens_ofs lf ty.
  pose proof C as C'. open_itc C'. change (2 ^ 3) with 8.
  assert (D : exists q, p = 16 * q). { apply Z.mod_divide in Hpal; [|lia_std]. destruct Hpal as [q Hq]. exists q. lia_std. }
  destruct D as [q ->]. replace (16 * q + 144) with ((2 * q + 18) * 8) by lia_std. apply Z_mod_mult.
Qed.

Lemma switch_t : forall Rb l M MD T,
  m_halted MD = None -> PR6 Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt -> 1 <= mx ->
  mem_wr R_segs M (sp - 208) 208 -> mem_wr R_segs M p 7160 ->
  mem_arr 2 R_segs M (p + 152) 320 lf -> mem_arr 2 R_segs M (p + 792) 288 (arr_get work1Ar) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA -> mem_arr 4 R_segs M (p + 1368) 1444 cf ->
  mem_u64 R_segs M (p + 144) (p + 1368 + 4 * nx) ->
  mem_arr 2 R_segs M 75186 31 (arr_get lbase_a) -> mem_arr 2 R_segs M 75248 31 (arr_get lext_a) ->
  mem_arr 2 R_segs M 75310 32 (arr_get dbase_a) -> mem_arr 2 R_segs M 75374 32 (arr_get dext_a) ->
  (forall R' M', CR R' [] -> SR st0 R' [] -> zget_l R' [] kT1 = t_len st0 - t_drop st0 -> zget_l R' [] kA2 = p + 792 + 2 * t_sym st0 ->
     mpost R_segs M M' (sp + -208) (sp + -168) 0 0 ->
     CM M' -> SM st0 M' -> SP st0 -> it_not_enough ty (itm_used rt) = false ->
     realizes R_segs (zcfg R_segs 139704 (zupd R' []) M' MD) T) ->
  (forall R' M', PR8 R' [] -> zget_l R' [] kA6 = 1 -> mpost R_segs M M' (sp + -208) (sp + -168) 0 0 ->
     it_not_enough ty (itm_used rt) = true ->
     realizes R_segs (zcfg R_segs 140556 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 139416 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 Hmx Wf Wp Hlens Hwork Hcnt Htbl Hnext Hlb Hle Hdb Hde KBODY KFAIL.
  pose proof C as C'. open_itc C'. open_pregs6_t HP. zkeys. xaddr_t. clear HtyC HtyD.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3).
  pose proof (spure_st0 _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as HSP.
  pose proof p144_al as P8.
  assert (HSM : forall Mq, mem_arr 2 R_segs Mq (sp + -136) 16 cA -> mem_arr 4 R_segs Mq (p + 1368) 1444 cf -> SM st0 Mq).
  { intros Mq A B. unfold smem_t. cbn [t_count t_tbl itm_st0]. split; [exact A|].
    eapply mem_arr_ext; [exact B|]. intros j _. symmetry. apply tblA_get. }
  pose proof (ne_pow _ _ _ _ _ _ _ _ _ _ _ _ _ C192' rt ltac:(lia)) as NEP.
  pose proof (mpost_stable R_segs M (sp + -208) (sp + -168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -208) (sp + -168) 0 0) M) by (apply mpost_refl).
  assert (J : forall RJ MJ, PR8 RJ [] -> zget_l RJ [] kT0 = mx -> zget_l RJ [] kT1 = mn -> zget_l RJ [] kA7 = rt ->
            zget_l RJ [] kT2 = it_match ty ->
            framed (fun X => mpost R_segs M X (sp + -208) (sp + -168) 0 0) MJ ->
            mem_wr R_segs MJ (sp - 208) 208 -> mem_wr R_segs MJ p 7160 ->
            mem_arr 2 R_segs MJ (p + 152) 320 lf -> mem_arr 2 R_segs MJ (p + 792) 288 (arr_get work1Ar) ->
            mem_arr 2 R_segs MJ (sp + -136) 16 cA -> mem_arr 4 R_segs MJ (p + 1368) 1444 cf ->
            mem_u64 R_segs MJ (p + 144) (p + 1368 + 4 * nx) ->
            mem_u64 R_segs MJ (sp + -208) (EXA ty p) -> mem_u64 R_segs MJ (sp + -192) (BSA ty p) -> mem_u64 R_segs MJ (sp + -184) (isL ty + isD ty) ->
            mem_arr 2 R_segs MJ (EXM ty p) (NE ty) (it_extra ty work1Ar) -> mem_arr 2 R_segs MJ (BSM ty p) (NE ty) (it_base ty work1Ar) ->
            realizes R_segs (zcfg R_segs 139548 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HPJ JT0 JT1 JA7 JA2 HAGJ WfJ WpJ HlensJ HworkJ HcntJ HtblJ HnextJ Hs0 Hs16 Hs24 HextJ HbaseJ.
    clear Wf Wp Hlens Hwork Hcnt Htbl Hnext Hlb Hle Hdb Hde HAG. open_pregs8 HPJ. zkeys. zrebase.
    zbr Rfd false.
    zstep Rfd. zsetreg 0 ltac:(symmetry; apply (land_mask0 (p + 144) 3); [lia_std | exact P8]).
    zbr Rfd false.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    destruct ty_cases_t as [(Ety & E0 & EM & EX & EB & EN & EL & ED) | [(Ety & E0 & EM & EX & EB & EN & EL & ED) | (Ety & E0 & EM & EX & EB & EN & EL & ED)]];
      rewrite E0 in LA0.
    -
      zbr Rfd true.
      zstep Rfd.
      zbr Rfd true.
      eapply init_t; try eassumption; try lia.
      all: try kauto_t. all: try (zregv; rewrite E0; reflexivity).
      + apply HSM; assumption.
      + intros R' M' HC' HS' L1 L2 HPO HM' HSM'. eapply KBODY; try eassumption.
        * eapply mpost_trans; [exact HAGJ | exact HPO].
        * rewrite NEP, Ety. reflexivity.
    -
      zbr Rfd false.
      zstep Rfd.
      destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
      + zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KFAIL Rx MJ) end.
        all: try kauto_t. all: try exact HAGJ.
        rewrite NEP, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
      + zbr Rfd false.
        zstep Rfd.
        zbr Rfd true.
        eapply init_t; try eassumption; try lia.
        all: try kauto_t. all: try (zregv; rewrite E0; reflexivity).
        * apply HSM; assumption.
        * intros R' M' HC' HS' L1 L2 HPO HM' HSM'. eapply KBODY; try eassumption.
          -- eapply mpost_trans; [exact HAGJ | exact HPO].
          -- rewrite NEP, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia].
    -
      zbr Rfd true.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
      + zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KFAIL Rx MJ) end.
        all: try kauto_t. all: try exact HAGJ.
        rewrite NEP, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
      + zbr Rfd false.
        eapply init_t; try eassumption; try lia.
        all: try kauto_t. all: try (zregv; rewrite E0; reflexivity).
        * apply HSM; assumption.
        * intros R' M' HC' HS' L1 L2 HPO HM' HSM'. eapply KBODY; try eassumption.
          -- eapply mpost_trans; [exact HAGJ | exact HPO].
          -- rewrite NEP, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia]. }
  zrebase.
  destruct ty_cases_t as [(Ety & E0 & EM & EX & EB & EN & EL & ED) | [(Ety & E0 & EM & EX & EB & EN & EL & ED) | (Ety & E0 & EM & EX & EB & EN & EL & ED)]];
    rewrite E0 in LA0.
  - zstep Rfd.
    zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    zbr Rfd false.
    zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J Rx Mx) end.
    all: try kauto_t. all: try (zregv; first [rewrite EM | rewrite E0]; reflexivity).
    all: rewrite ?EX, ?EB, ?EN, ?Ety; try assumption.
    all: try (cbn [EXM BSM it_extra it_base]; eapply mem_arr_ext; [exact Hwork|]; intros; reflexivity).
  - zstep Rfd.
    zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    zbr Rfd true.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J Rx Mx) end.
    all: try kauto_t. all: try (zregv; first [rewrite EM | rewrite E0]; reflexivity).
    all: rewrite ?EX, ?EB, ?EN, ?Ety; try assumption.
  - zstep Rfd.
    zbr Rfd true.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J Rx Mx) end.
    all: try kauto_t. all: try (zregv; first [rewrite EM | rewrite E0]; reflexivity).
    all: rewrite ?EX, ?EB, ?EN, ?Ety; try assumption.
Qed.

Lemma epilogue_t : forall Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  m_halted MD = None -> zget_l Rb l kSP = sp + -208 -> zget_l Rb l kA6 = v ->
  slots_t M v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 -> Z.land v1 (-2) = v1 -> 0 <= v1 < two64 ->
  (forall R', zget_l R' [] kA0 = v -> zget_l R' [] kSP = sp -> zget_l R' [] kRA = v1 ->
     zget_l R' [] kS0 = v8 -> zget_l R' [] kS1 = v9 -> zget_l R' [] kS2 = v18 -> zget_l R' [] kS3 = v19 ->
     zget_l R' [] kS4 = v20 -> zget_l R' [] kS5 = v21 -> zget_l R' [] kS6 = v22 -> zget_l R' [] kS7 = v23 ->
     zget_l R' [] kS8 = v24 -> zget_l R' [] kS9 = v25 -> zget_l R' [] kS10 = v26 -> zget_l R' [] kS11 = v27 ->
     zget_l R' [] kGP = zget_l Rb l kGP -> zget_l R' [] kTP = zget_l Rb l kTP ->
     realizes R_segs (zcfg R_segs v1 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 140556 (zupd Rb l) M MD) T.
Proof using C zc ret pb p wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hh LSP LA6 HSL Hev Hv1 K.
  remember (zget_l Rb l kGP) as vgp' eqn:EG. remember (zget_l Rb l kTP) as vtp' eqn:ET. symmetry in EG, ET.
  pose proof C as C'. open_itc C'. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  unfold slots_t in HSL. destruct HSL as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
  zrebase.
  zstep Rfd.
  do 13 (zstep Rfd).
  zstep Rfd.
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
  all: zreg.
Qed.

Lemma setbits_t : forall Rb l M MD T rv,
  m_halted MD = None -> pregs3_t Rb l -> zget_l Rb l kA4 = pb -> zget_l Rb l kA7 = rv -> mem_wr R_segs M p 7160 ->
  (forall R' M', pregs3_t R' [] -> zget_l R' [] kA6 = 0 -> mpost R_segs M M' pb (pb + 4) 0 0 -> mem_u32 R_segs M' pb rv ->
     realizes R_segs (zcfg R_segs 140556 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 140548 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T rv Hh HP LA4 LA7 Wp K.
  pose proof C as C'. open_itc C'. unfold pregs3_t in HP. destruct HP as (LSP & LGP & LTP). zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15. unfold ZSEP in Hpb.
  pose proof (mpost_stable R_segs M pb (pb + 4) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X pb (pb + 4) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
  all: try kauto_t. all: try close_pregs3_t. all: exact HAG.
Qed.

Lemma it_room_ge_t : 128 <= it_room ty.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia_std. Qed.

Lemma break_tail_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> zget_l Rb l kT1 = 256 * (t_len st - t_drop st) ->
  CM M -> SM st M -> SP st ->
  0 <= t_len st - t_drop st <= 15 -> 0 <= t_used st < 65536 -> 0 <= t_huff st ->
  (t_huff st <> 0 -> 0 <= t_next st + t_huff st < 1444) ->
  (forall R' M', pregs3_t R' [] -> zget_l R' [] kA6 = 0 -> mpostL R_segs M M' rsT ->
     mem_arr 4 R_segs M' (p + 1368) 1444
       (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                 else t_tbl st)) ->
     mem_u64 R_segs M' (p + 144) (p + 1368 + 4 * (nx + t_used st)) -> mem_u32 R_segs M' pb rt ->
     mem_wr R_segs M' (sp - 208) 208 -> mem_wr R_segs M' p 7160 ->
     mem_arr 2 R_segs M' (p + 152) 320 lf -> mem_arr 2 R_segs M' (p + 792) 288 (arr_get work1Ar) ->
     realizes R_segs (zcfg R_segs 140556 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 140440 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT1 HM HSM HP Hhb Hused Hhuff Hfit K.
  pose proof C as C'. open_itc C'. open_cmem_t HM. open_smem_t HSM. open_spure HP. zkeys. xaddr_t.
  clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15 LOWR DROPR.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192') as RTF. pose proof it_room_ge_t as HRG.
  assert (J20 : forall RJ MJ, pregs3_t RJ [] -> zget_l RJ [] kA3 = p + 144 -> zget_l RJ [] kA4 = pb -> zget_l RJ [] kA7 = rt ->
            zget_l RJ [] kT5 = t_used st ->
            mpost R_segs M MJ (p + 1368) (p + 7144) 0 0 ->
            mem_arr 4 R_segs MJ (p + 1368) 1444
              (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                        else t_tbl st)) ->
            mem_wr R_segs MJ (sp - 208) 208 -> mem_wr R_segs MJ p 7160 ->
            mem_arr 2 R_segs MJ (p + 152) 320 lf -> mem_arr 2 R_segs MJ (p + 792) 288 (arr_get work1Ar) ->
            mem_u64 R_segs MJ (p + 144) (p + 1368 + 4 * nx) ->
            realizes R_segs (zcfg R_segs 140496 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HPJ JA3 JA4 JA7 JT5 HPO HtblJ WfJ WpJ HlensJ HworkJ HnextJ.
    clear Hcnt Htbl Wf Wp Hlens Hwork Hnext Hsl0 Hsl8 Hsl16 Hsl24 Hsl32 Hext Hbase. unfold pregs3_t in HPJ. destruct HPJ as (LSP & LGP & LTP). zkeys.
    pose proof (mpost_stable R_segs MJ (p + 144) (p + 152) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
    assert (HAG : framed (fun X => mpost R_segs MJ X (p + 144) (p + 152) 0 0) MJ) by (apply mpost_refl).
    zrebase.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zsetreg (4 * t_used st) ltac:(symmetry; apply zext32_x4; lia).
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    zsetreg 1 ltac:(rewrite !Z.mod_small by lia; destruct (Z.ltb_spec 0 (p + 1368 + 4 * nx)); [|lia];
                    destruct (Z.ltb_spec (4 * t_used st + (p + 1368 + 4 * nx)) 1); [lia|]; reflexivity).
    zbr Rfd false.
    zstep Rfd. zsetreg (t_used st) ltac:(symmetry; apply zext32_id; lia).
    zstep Rfd. zsetreg (4 * t_used st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep Rfd. zsetreg (p + 1368 + 4 * (nx + t_used st)) ltac:(lia).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_t Rx [] Mx MD T rt Hh) end.
    all: try kauto_t. all: try close_pregs3_t.
    intros R' M' HP' LA6 HPO2 Hbits'.
    destruct HPO2 as [HA2 HW2].
    eapply K; try eassumption.
    - pose proof (framed_mpostL_trans2 R_segs M M MJ rsT _ _ _ _ (mpostL_refl R_segs M rsT) HPO ltac:(left; cbn; left; lia) ltac:(right; lia)) as F1.
      pose proof (framed_mpostL_trans2 R_segs M MJ _ rsT _ _ _ _ F1 HAG ltac:(left; cbn; right; left; lia) ltac:(right; lia)) as F2.
      exact (framed_mpostL_trans2 R_segs M _ M' rsT _ _ _ _ F2 (conj HA2 HW2) ltac:(left; cbn; right; right; left; unfold ZSEP in Hpb; lia) ltac:(right; lia)).
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_u64_magree; [exact HA2 | eassumption | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    - apply HW2. assumption.
    - apply HW2. assumption.
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia]. }
  pose proof (mpost_stable R_segs M (p + 1368) (p + 7144) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1368) (p + 7144) 0 0) M) by (apply mpost_refl).
  open_cregs_t HC. open_sregs_t HS. zkeys. zrebase.
  destruct (Z.eq_dec (t_huff st) 0) as [H0|HN0].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J20 Rx M) end.
    all: try kauto_t. all: try close_pregs3_t. all: try assumption.
    rewrite H0. cbn [Z.eqb negb]. exact Htbl.
  - zbr Rfd false.
    specialize (Hfit HN0).
    destruct (arr4_hole R_segs M (p + 1368) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd. zsetreg (4 * t_huff st) ltac:(symmetry; apply zext32_x4; lia).
    zstep Rfd.
    zbr Rfd false.
    zbr Rfd false.
    zstep Rfd. zsetreg (t_huff st) ltac:(symmetry; apply zext32_id; lia).
    zstep Rfd. zsetreg (4 * t_huff st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep Rfd.
    zstep Rfd. zsetreg (64 + 256 * (t_len st - t_drop st))
      ltac:(replace (256 * (t_len st - t_drop st)) with (Z.shiftl (t_len st - t_drop st) 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
            rewrite Z.lor_comm, lor_shiftl_add by (try (change (2 ^ 8) with 256); lia); rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
    zstep Rfd. zsetreg 0 ltac:(symmetry; rewrite srli_small by lia; apply Z.div_small; change (2 ^ 16) with 65536; lia).
    zstep Rfd.
    zstep Rfd.
    match goal with
    | Hlo : mem_u16 _ ?Mc _ (64 + 256 * (t_len st - t_drop st)), Hhi : mem_u16 _ _ _ 0 |- _ =>
      pose proof (entry_write2_t Mc (p + 1368) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) _ 0 _ _ HT1 HT2 Hlo Hhi
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
      clear Hlo Hhi HT1 HT2
    end.
    rewrite (Z.mod_small (64 + 256 * (t_len st - t_drop st))) in Htbl by lia.
    replace (64 + 256 * (t_len st - t_drop st) + 65536 * 0) with (code_pack 64 (t_len st - t_drop st) 0) in Htbl by (rewrite code_pack_small by lia; lia).
    apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J20 Rx Mx) end.
    all: try kauto_t. all: try close_pregs3_t. all: try assumption.
    destruct (Z.eqb_spec (t_huff st) 0); [lia|]. cbn [negb]. exact Htbl.
Qed.

Lemma max0_t : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> mx = 0 ->
  mem_wr R_segs M p 7160 -> mem_arr 4 R_segs M (p + 1368) 1444 cf -> mem_u64 R_segs M (p + 144) (p + 1368 + 4 * nx) ->
  mem_wr R_segs M (sp - 208) 208 -> mem_arr 2 R_segs M (p + 152) 320 lf -> mem_arr 2 R_segs M (p + 792) 288 wf ->
  (forall R' M', pregs3_t R' [] -> zget_l R' [] kA6 = 0 -> mpostL R_segs M M' rsT ->
     mem_arr 4 R_segs M' (p + 1368) 1444 (arr_get (arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0))) ->
     mem_u64 R_segs M' (p + 144) (p + 1368 + 4 * (nx + 2)) -> mem_u32 R_segs M' pb 1 ->
     mem_wr R_segs M' (sp - 208) 208 -> mem_wr R_segs M' p 7160 ->
     mem_arr 2 R_segs M' (p + 152) 320 lf -> mem_arr 2 R_segs M' (p + 792) 288 wf ->
     realizes R_segs (zcfg R_segs 140556 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 140652 (zupd Rb l) M MD) T.
Proof using C zc ret bits.
  intros Rb l M MD T Hh HP Hmx0 Wp Htbl Hnext Wf Hlens Hwork K.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear Hprom HtyC HtyD Hlf Hwf Hlens15.
  pose proof it_room_ge_t as HRG.
  assert (Htbl' : mem_arr 4 R_segs M (p + 1368) 1444 (arr_get (tblA cf))).
  { eapply mem_arr_ext; [exact Htbl|]. intros j _. symmetry. apply tblA_get. }
  clear Htbl.
  pose proof (mpostL_stable R_segs M rsT ltac:(cbn; unfold ZSEP in Hpb; rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X rsT) M) by (apply mpostL_refl).
  destruct (arr4_hole R_segs M (p + 1368) 1444 (arr_get (tblA cf)) nx Htbl' ltac:(lia)) as [HT1 HT2]. clear Htbl'.
  zrebase.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2_t Mc (p + 1368) 1444 (arr_get (tblA cf)) nx 320 0 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  change (320 mod 65536 + 65536 * 0) with 320 in Htbl.
  apply mem_arr_arr_set in Htbl; [| unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  destruct (arr4_hole R_segs _ (p + 1368) 1444 _ (nx + 1) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2_t Mc (p + 1368) 1444 _ (nx + 1) 320 0 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  change (320 mod 65536 + 65536 * 0) with 320 in Htbl.
  apply mem_arr_arr_set in Htbl; [| rewrite arr_len_set; unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_t Rx [] Mx MD T 1 Hh) end.
  all: try kauto_t. all: try close_pregs3_t.
  intros R' M' HP' LA6 HPO2 Hbits'. destruct HPO2 as [HA2 HW2].
  eapply K; try eassumption.
  - exact (framed_mpostL_trans2 R_segs M _ M' rsT _ _ _ _ HAG (conj HA2 HW2) ltac:(left; cbn; right; right; left; unfold ZSEP in Hpb; lia) ltac:(right; lia)).
  - eapply mem_arr_magree; [exact HA2 | | unfold ZSEP in Hpb; lia | lia].
    change (code_pack 64 1 0) with 320. exact Htbl.
  - eapply mem_u64_magree; [exact HA2 | | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    match goal with H : mem_u64 _ _ (p + 144) ?v |- _ => replace (p + 1368 + 4 * (nx + 2)) with v by lia; exact H end.
  - apply HW2. assumption.
  - apply HW2. assumption.
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
Qed.
End U7IT6.
End FXG.
