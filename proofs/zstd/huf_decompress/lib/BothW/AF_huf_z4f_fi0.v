(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame Mem Step.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_hdefs AF_huf_w4s3b AF_huf_z4f_defs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Definition x42f0_h (P : Prop) : Prop := P.
Lemma x42f0_hi : forall P : Prop, P -> x42f0_h P.
Proof. intros P H. exact H. Qed.
Definition x42f0_g (P : Prop) : Prop := P.
Lemma x42f0_gi : forall P : Prop, P -> x42f0_g P.
Proof. intros P H. exact H. Qed.

Local Ltac x42f0_lia1 :=
  first [ lia
        | match goal with H : x42f0_h ?P |- _ => let H' := fresh "HU" in assert (H' : P) by exact H; lia end ].

Local Ltac x42f0_uz :=
  w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; x42f0_lia1.

Local Ltac x42f0_csz :=
  repeat match goal with |- context [Z.of_nat (cells_size ?cs)] =>
    let v := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with v end;
  cbn [Z.of_nat Pos.of_succ_nat].

Local Ltac x42f0_csz_in H :=
  repeat match type of H with context [Z.of_nat (cells_size ?cs)] =>
    let v := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with v in H end.

Local Ltac x42f0_wv W :=
  lazymatch goal with |- wview _ _ (wa ?X) <> None =>
    lazymatch type of W with wr_at _ _ ?A _ =>
      replace X with (A + (X - A)) by lia; apply (proj2 (proj2 W)); lia end end.

Local Ltac x42f0_xb :=
  lazymatch goal with |- bv_unsigned (edenot ?E ?X) < _ =>
    w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
    repeat match goal with |- context [2 ^ (?s mod 64)] =>
      let t := eval vm_compute in (2 ^ (s mod 64)) in change (2 ^ (s mod 64)) with t end;
    repeat match goal with |- context [?x / 9007199254740992] =>
      let HV := fresh "HV" in let v := fresh "v" in
      assert (HV : 0 <= x / 9007199254740992 < 2048) by (Z.div_mod_to_equations; lia);
      set (v := x / 9007199254740992) in *; clearbody v end;
    rewrite ?Z.mod_small by lia; lia
  end.

Local Ltac x42f0_shd :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      apply (z4f_shd_ap E X B O k w); [ x42f0_xb | lia | lia | lia | w4uz | w4uz | x42f0_uz ]
  end.

Local Ltac x42f0_sok LC :=
  lazymatch goal with |- store_ok ?segs ?m (adenot ?E {| a_base := ?b; a_off := ?o |}) 8 = true =>
    lazymatch type of LC with rw_cells _ _ (?S + ?d) _ =>
      let k := eval vm_compute in (Z.to_nat (o - d)) in
      rewrite adenot_wa; eapply (rw_cells_store_ok_at segs m (S + d) _ k _ 8%nat _ LC);
      [ reflexivity | reflexivity
      | unfold estart; cbn [a_base a_off]; w4ez; unfold wa; f_equal;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia ]
    end
  end.

Local Ltac x42f0_evr :=
  repeat match goal with |- context [bv_unsigned (ev ?E ?j)] =>
    lazymatch goal with
    | _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail
    | _ => let H := fresh "EVR" in kx_erange H (EVar j); cbn [edenot] in H
    end
  end; lia.

Local Ltac x42f0_lba :=
  lazymatch goal with
  | |- LBW ?p (ev ?E ?a) => change (LBW p (edenot E (EVar a))); x42f0_lba
  | |- LBW ?p (edenot ?E (EVar ?a)) =>
      w4ez; rewrite ?OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib.MState.Z_to_bv_bv_unsigned;
      first [ assumption | eapply lbw_mono; [eassumption | lia] ]
  end.

Local Ltac x42f0_lbw :=
  lazymatch goal with
  | |- LBW 19 (edenot ?E (EAlu ALU_SLL ?X ?Y)) =>
      apply (lbw_sll 8 11 (edenot E X) (edenot E Y)); [ x42f0_lba | e42_amt | lia ]
  end.

Section CANSEC1. Context {rc : runConstT}.
Section X42E.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT DTB tl lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42e_ctx SPV DST dcap SRC n DT DTB tl lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis ACTX : x42e_actx RNG m0 SPV DST dcap SRC n DT DTB lo.
  Variable POST : machine_state -> Prop.
  Hypothesis TL11 : tl = 11.
  Hypothesis FI1 : x42e_fi1_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST.

  Lemma x42e_fi0 : x42e_fi0_stmt RNG gp tp F fc m0 SPV DST dcap SRC n DT src dtb POST.
  Proof using CTX X2OK NBOK ACTX TL11 FI1.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    unfold x42e_fi0_stmt.
    intros r mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 e0 e1 e2 e3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x1 x5 x6 x16 x17 x18 x19 x25 w0 w1 w2
      MU WM MU0 WM0 MI OUT DTBH FR AR LC SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN
      HLBc0 HLBc1 HLBc2 HLBc3 KH KO. subst nd.
    rewrite TL11 in DTBF. change (4 + 4 * 2 ^ 11) with 8196 in DTBF.
    assert (DPOS : 0 < dcap) by lia.
    pose proof (RDST DPOS) as RDSTc. pose proof (RDSTS DPOS) as RDSTSc.
    assert (UU : unpoisoned mm SRC (SRC + n) /\ unpoisoned mm DT (DT + DTB) /\ (0 < dcap -> unpoisoned mm DST (DST + dcap)))
      by (eapply x42f_unp; eassumption).
    destruct UU as (_ & UDTm & UDSTm'). pose proof (UDSTm' DPOS) as UDSTm. clear UDSTm'.
    assert (RLOC : rng RNG (SPV + -232) 128) by (eapply rng_sub; [exact RSTK | lia | lia]).
    assert (WAD : wr_at bsegs mm DST dcap).
    { pose proof OUT as (S0 & S1 & S2). split; [lia | split; [lia |]]. intros i Hi. apply (S2 (DST + i)). lia. }
    assert (TAB : ztab_fact bsegs mm (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)]) by (eapply x42f_tab; eassumption).
    unfold shspan in RDTS, RDSTSc.
    apply x42f0_gi in HOL; apply x42f0_gi in HO2; apply x42f0_gi in HO3; apply x42f0_gi in HE2; apply x42f0_gi in HE3; apply x42f0_gi in HOLR;
    apply x42f0_gi in HI0; apply x42f0_gi in HI1; apply x42f0_gi in HI2; apply x42f0_gi in HI3; apply x42f0_gi in HN0; apply x42f0_gi in HN1;
    apply x42f0_gi in HN2; apply x42f0_gi in HN3; apply x42f0_gi in HL1; apply x42f0_gi in HL2; apply x42f0_gi in HL3; apply x42f0_gi in HLN;
    apply x42f0_gi in SL; apply x42f0_gi in R2; apply x42f0_gi in DT2; apply x42f0_gi in DTA.
    apply x42f0_hi in DJ1; apply x42f0_hi in OS2; apply x42f0_hi in DSTA.
    clear UDST RDST RDSTS UDT USRC RSRC RSRCS RSTK.
    kx_runFm [546176] 140%nat
      [KZTab (DT + 4) 8192 4 [(2, 0, 11); (3, 1, 2)];
       KZRange (bv_unsigned c0) 0 (2^64 - 1); KZRange (bv_unsigned c1) 0 (2^64 - 1);
       KZRange DST 4096 (2^47 - 1); KZRange dcap 10 (2^32 - 1); KZRange o0 0 (2^32 - 1); KZRange o1 0 (2^32 - 1);
       KZRange (DST + o0) 4096 (2^47 - 10); KZRange (DST + o1) 4096 (2^47 - 10);
       KZRange DT 4096 (2^47 - 8196); KZRange DTB 8196 (2^47 - 1); KZRange SPV 8192 (2^47 - 1);
       KZWr (DST + o0) 2; KZWr (DST + o1) 2;
       KZDisj (DST + o0) 2 DT DTB; KZDisj (DST + o1) 2 DT DTB; KZDisj (SPV + -232) 128 DT DTB;
       KZDisj (DST + o0) 2 (SPV + -232) 128; KZDisj (DST + o1) 2 (SPV + -232) 128]
      [(DT, DTB)]
      [(DT, DTB); (DST, dcap); (SPV + -232, 128)]
      [(DT + 4, 8192); (DST + o0, 2); (DST + o1, 2)].
    all: apply x42f0_hi in DJ2; apply x42f0_hi in OS3.
    all: lazymatch goal with
      | |- evtF _ _ _ _ => idtac
      | |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range _ w); unfold bv_modulus in *; lia
      | |- 0 <= bv_unsigned ?w <= _ => pose proof (bv_unsigned_in_range _ w); unfold bv_modulus in *; lia
      | |- store_ok _ _ _ _ = true => x42f0_sok LC
      | |- flat _ _ _ /\ _ => clear OS1; x42f0_shd
      | |- accP _ _ _ => z4facc RDSTc
      end.
    kx_post_regs.
    lazymatch goal with |- context [mem_denot ?E mm ?lg] => assert (LWR : log_wr bsegs mm E lg) end.
    { pose proof (proj2 LC) as WLC. x42f0_csz_in WLC.
      cbn [log_wr]. repeat split; intros j Hj; simpl in Hj;
      unfold estart; cbn [a_base a_off]; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
      first [ x42f0_wv WAD | x42f0_wv WLC ]. }
    pose proof (kx_mem_inv_log bsegs KXE mm _ MI KXLF LWR) as MI1. clear MI LWR.
    kx_post_mem_free. kx_munch MU. kx_munch MU0.
    kx_frame DTBH. kx_frame SRCB. kx_frame FR. kx_frame AR.
    all: try (lazymatch goal with |- _ \/ _ => unfold x42f0_g in *; x42f0_csz; x42f0_lia1 end).
    kx_cells_split LC; kx_cells_post.
    replace (Z_to_bv 64 (-16)) with (Z_to_bv 64 18446744073709551600) by (apply bv_eq; vm_compute; reflexivity).
    rewrite ?OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib.MState.Z_to_bv_bv_unsigned in *.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?U0)) _ (Z_to_bv 64 (DST + ?U1))
                                            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      eapply (FI1 r mb _ q OL (- DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 U0 U1) end.
    all: unfold x42f0_g in *.
    all: lazymatch goal with
      | |- LBW 19 _ => x42f0_lbw
      | |- rw_cells _ _ (SPV + -232) _ => kx_cells_merge
      | |- context [ev _ _] => x42f0_evr
      | |- _ \/ _ => x42f0_csz; x42f0_lia1
      | |- Z.le _ _ => first [assumption | lia]
      | |- Z.lt _ _ => first [assumption | lia]
      | |- and (Z.le _ _) _ => first [assumption | lia]
      | |- le _ _ => first [assumption | lia]
      | |- @eq Z _ _ => lia
      | |- _ => first [exact KH | exact KO | eassumption]
      end.
  Qed.
End X42E.
End CANSEC1.
