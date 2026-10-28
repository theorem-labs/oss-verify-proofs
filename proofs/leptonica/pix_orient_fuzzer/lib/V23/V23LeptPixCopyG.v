(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptUb V23LeptErr V23LeptCmap V23LeptCmapValid V23LeptCmap2 V23MemcpyBase V23Memcpy V23LeptPixCopyAT V23LeptPixCopyGC V23LeptPma1G V23LeptCloseIface V23_code_6e000_6f000 V23LeptPixCopyST.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyGC O23LeptPixCopyG.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCopyT O23LeptPixCopyST O23LeptPma1G O23LeptCloseIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).

Section PixCopyG.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).


(* [comment removed for export] *)
Definition PCGM (m : word -> option byte) (s pixd pixs spp : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
     (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 spp)))
     (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
     (Z_to_bv 64 (pixd + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
     (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x6ed38)))
     (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
     (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 pixs)))
     (Z_to_bv 64 (pixd + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

Section Segs.
Variable rom : word -> option byte.

  Lemma pcggAB_mulw : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> (0 <= a * b < 2 ^ 31)%Z ->
    v_mulw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof. intros a b Ha Hb Hab. unfold v_mulw. rewrite !u_Z2bv by lia. rewrite (sw32_eq (a * b)), (sw32_small (a * b)) by lia. reflexivity. Qed.

  Lemma pcggAB_add : forall a b : Z, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
  Proof. intros a b. rewrite <- alu_add. apply ex_ptr_val. Qed.

  Lemma pcggAB_srlw30 : forall a : Z, (0 <= a < 2 ^ 30)%Z -> v_srlw (Z_to_bv 64 a) (Z_to_bv 64 30) = Z_to_bv 64 0.
  Proof.
    intros a Ha. unfold v_srlw. rewrite !u_Z2bv by lia. rewrite (bv_wrap_small 32 a) by (unfold bv_modulus; lia).
    change (30 mod 32)%Z with 30%Z. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
  Qed.

  Ltac pcggAB_norm :=
    rewrite ?w_mulw, ?m_mul;
    repeat first [ rewrite ex_sx32 by lia | rewrite ex_sllw_small by lia | rewrite pcggAB_mulw by lia | rewrite zbv_mul
                 | rewrite pcggAB_add | rewrite pcggAB_srlw30 by lia ].

  Ltac pcggAB_fin := ex_vnorm; pcggAB_norm; first [reflexivity | f_equal; lia | f_equal; nia].

  Ltac pcggAB_sc := ex_vnorm; pcggAB_norm; ex_br.

  (* [comment removed for export] *)
  Lemma pcg_A : forall regs m (s pixd pixs : Z) (vs : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= pixs)%Z -> pixd <> pixs -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 48 \/ s <= pixs)%Z ->
    (0 < 4 * (p_wpl vs * p_h vs) < 2 ^ 31)%Z -> (0 <= p_wpl vs * p_h vs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6eb5c : word) m rom) (mkst regs' (0x6edec : word) (O23LeptCmap2.FR5 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x6ebc4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 (4 * (p_wpl vs * p_h vs))
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs vs ret Hs Hs64 Hpd Hps NE ALs PXs DJ Hwh Hwh0 SOK H2 H1 H10 H11.
    pose proof PXs as (Hp0 & Hp64 & WFs & _).
    pose proof (wf_w _ WFs) as Bw. pose proof (wf_h _ WFs) as Bh. pose proof (wf_d _ WFs) as Bd.
    pose proof (wf_spp _ WFs) as Bspp. pose proof (wf_wpl _ WFs) as Bwpl.
    assert (Hh1 : (1 <= p_h vs)%Z) by nia. assert (Hw1 : (1 <= p_wpl vs)%Z) by nia.
    assert (Hle : (p_wpl vs <= p_wpl vs * p_h vs)%Z) by nia.
    pose proof (PIX_rd_w SEGS m pixs vs PXs) as Rw. pose proof (PIX_rd_h SEGS m pixs vs PXs) as Rh.
    pose proof (PIX_rd_d SEGS m pixs vs PXs) as Rd. pose proof (PIX_rd_spp SEGS m pixs vs PXs) as Rspp.
    pose proof (PIX_rd_wpl SEGS m pixs vs PXs) as Rwpl.
    replace (0x6eb5c : word) with (Z_to_bv 64 0x6eb5c) by (apply bv_eq; reflexivity).
    replace (0x6edec : word) with (Z_to_bv 64 0x6edec) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pixd; pixs; p_w vs; p_h vs; p_d vs; p_spp vs; p_wpl vs]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; pixs; p_w vs; p_h vs; p_d vs; p_spp vs; p_wpl vs]%Z) m
      [KRange (EVar 32) 48 (2 ^ 64 - 1); KWr (SA (EVar 32) (-48)) 48;
       KRange (EVar 33) 1 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 64 - 65); KAlign (EVar 34) 8;
       KDisj (SA (EVar 32) (-48)) 48 (SA (EVar 34) 0) 64;
       KWord (SA (EVar 34) 0) 4 (EVar 35); KWord (SA (EVar 34) 4) 4 (EVar 36); KWord (SA (EVar 34) 8) 4 (EVar 37);
       KWord (SA (EVar 34) 12) 4 (EVar 38); KWord (SA (EVar 34) 16) 4 (EVar 39);
       KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1);
       KRange (EVar 38) 0 (2 ^ 31 - 1); KRange (EVar 39) 0 (2 ^ 31 - 1)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 600%nat [0x6edec]%Z (SCR [false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R'. split.
      - unfold O23LeptCmap2.FR5. ex_mem regs Hms.
      - repeat split. all: try (ex_reg regs HR'; pcggAB_fin). ex_agree HR HR'. }
    all: pcggAB_sc.
  Qed.

  (* [comment removed for export] *)
  Lemma pcg_B : forall regs m (pixd pixs : Z),
    getr regs 10 = Z_to_bv 64 0 -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6ebc4 : word) m rom) (mkst regs' (0x6e4cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x6ec94 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H10 H8 H9.
    replace (0x6ebc4 : word) with (Z_to_bv 64 0x6ebc4) by (apply bv_eq; reflexivity).
    replace (0x6e4cc : word) with (Z_to_bv 64 0x6e4cc) by (apply bv_eq; reflexivity).
    ex_entry regs [pixd; pixs]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [pixd; pixs]%Z) m []%Z) by (unfold know_ok; apply Forall_nil).
    ex_run 100%nat [0x6e4cc]%Z (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split. all: try (ex_reg regs HR'). ex_agree HR HR'.
  Qed.

  Import SymExec2 SymExec2Sound SymRun LeptExec. Import SX2. Import SX2S.

  Ltac pcggCD_beq regs :=
    first [ reflexivity
          | solve [f_equal; ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
                   repeat match goal with H : getr regs _ = _ |- _ => rewrite H end;
                   rewrite ?ex_sx32 by lia; first [reflexivity | f_equal; lia]]
          | solve [ex_bytes_eq regs] ].

  Ltac pcggCD_mem regs Hms :=
    eapply ex_msteps_mem; [exact Hms | cbn [mem_denot s_log e_addr e_width e_val];
      repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | pcggCD_beq regs ]); reflexivity].

  Ltac pcggCD_reg regs HR' :=
    lazymatch goal with
    | |- getr _ ?k = _ =>
        rewrite (reg_val _ _ _ k HR');
        match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
        ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
        repeat match goal with H : getr regs _ = _ |- _ => rewrite H end;
        rewrite ?w_addw, ?ex_ptr_val; rewrite ?v_addw_Z; rewrite ?sw32_small by lia;
        first [reflexivity | (f_equal; lia)]
    end.

  (* [comment removed for export] *)
  Lemma pcg_C : forall regs m (s pixs pixd : Z) (vs vd : pixv),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (1 <= pixd)%Z -> (pixd mod 8 = 0)%Z -> PIXat m pixs vs -> PIXat m pixd vd ->
    (1 <= p_spp vs)%Z -> p_xres vs = 0%Z -> p_yres vs = 0%Z -> p_fmt vs = 0%Z -> p_text vs = 0%Z -> p_text vd = 0%Z ->
    (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z -> (pixd + 64 <= s - 80 \/ s <= pixd)%Z -> (pixs + 64 <= s - 80 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> store_ok SEGS m (Z_to_bv 64 (s - 80)) 32 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6ec94 : word) m rom) (mkst regs' (0x6ed38 : word) (PCGM m s pixd pixs (p_spp vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 19]%list) regs regs'.
  Proof.
    intros regs m s pixs pixd vs vd Hs Hs64 Hps Hpd Hpda PXs PXd Hspp Hxr Hyr Hfm Hts Htd Hsd Hds Hss SOKd SOKs H2 H8 H9.
    pose proof PXs as PXs'. destruct PXs' as (Ps0 & Ps1 & WFs & HBs). destruct WFs.
    pose proof PXd as PXd'. destruct PXd' as (Pd0 & Pd1 & WFd & _). destruct WFd.
    pose proof (PIX_rd_spp SEGS m pixs vs PXs) as Rspp.
    pose proof (PIX_rd_fmt SEGS m pixs vs PXs) as Rfmt. rewrite Hfm in Rfmt.
    pose proof (PIX_rd_text SEGS m pixs vs PXs) as Rts. rewrite Hts in Rts.
    pose proof (PIX_rd_text SEGS m pixd vd PXd) as Rtd. rewrite Htd in Rtd.
    assert (R24 : rdn SEGS m (Z_to_bv 64 (pixs + 24)) 8 = Some (Z_to_le_bytes 8 0)).
    { pose proof (bytes_at_field SEGS m pixs (pix_bytes vs) 24 8 ltac:(lia) ltac:(rewrite pix_bytes_len; cbn; lia)
                    ltac:(rewrite pix_bytes_len; cbn; lia) HBs) as X.
      change (Z.of_nat 24) with 24%Z in X. rewrite X. f_equal. unfold pix_bytes. rewrite Hxr, Hyr. reflexivity. }
    replace (0x6ec94 : word) with (Z_to_bv 64 0x6ec94) by (apply bv_eq; reflexivity).
    replace (0x6ed38 : word) with (Z_to_bv 64 0x6ed38) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pixs; pixd; p_spp vs]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixs; pixd; p_spp vs]%Z) m
      [KRange (EVar 32) 80 (2 ^ 64 - 1); KWr (SA (EVar 32) (-80)) 32; KWr (SA (EVar 34) 0) 64;
       KRange (EVar 33) 1 (2 ^ 64 - 65); KRange (EVar 34) 1 (2 ^ 64 - 65);
       KDisj (SA (EVar 33) 0) 64 (SA (EVar 34) 0) 64;
       KDisj (SA (EVar 32) (-80)) 80 (SA (EVar 34) 0) 64; KDisj (SA (EVar 32) (-80)) 80 (SA (EVar 33) 0) 64;
       KWord (SA (EVar 33) 12) 4 (EVar 35); KRange (EVar 35) 1 (2 ^ 31 - 1);
       KWord (SA (EVar 33) 24) 8 (ELit 0); KWord (SA (EVar 33) 32) 4 (ELit 0); KWord (SA (EVar 33) 40) 8 (ELit 0);
       KWord (SA (EVar 34) 40) 8 (ELit 0); KAlign (EVar 34) 8]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 1500%nat [0x6ed38]%Z (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - unfold PCGM. pcggCD_mem regs Hms.
    - repeat split; try (pcggCD_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma pcg_D : forall regs m (s pixd pixs : Z) (vd vs : pixv) (nb : Z),
    (1 <= pixd)%Z -> (p_data vd mod 4 = 0)%Z -> (p_data vs mod 4 = 0)%Z -> (0 <= nb < 2 ^ 31)%Z -> (1 <= pixs)%Z -> PIXat m pixd vd -> PIXat m pixs vs ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 nb ->
    exists regs',
      msteps SEGS (mkst regs (0x6ed38 : word) m rom) (mkst regs' (0x11e154 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x6ed54
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 (p_data vs) /\ getr regs' 12 = Z_to_bv 64 nb
      /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 nb
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs vd vs nb Hpd Hdd Hds Hnb Hps PXd PXs H2 H8 H9 H18.
    pose proof PXs as PXs'. destruct PXs' as (Ps0 & Ps1 & WFs & _). destruct WFs.
    pose proof PXd as PXd'. destruct PXd' as (Pd0 & Pd1 & WFd & _). destruct WFd.
    pose proof (PIX_rd_data SEGS m pixs vs PXs) as Rds.
    pose proof (PIX_rd_data SEGS m pixd vd PXd) as Rdd.
    replace (0x11e154 : word) with (Z_to_bv 64 0x11e154) by (apply bv_eq; reflexivity).
    replace (0x6ed38 : word) with (Z_to_bv 64 0x6ed38) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pixd; pixs; nb; p_data vd; p_data vs]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; pixs; nb; p_data vd; p_data vs]%Z) m
      [KRange (EVar 33) 1 (2 ^ 64 - 65); KRange (EVar 34) 1 (2 ^ 64 - 65);
       KWord (SA (EVar 33) 56) 8 (EVar 36); KWord (SA (EVar 34) 56) 8 (EVar 37); KAlign (EVar 36) 4; KAlign (EVar 37) 4]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 800%nat [0x11e154]%Z (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (pcggCD_reg regs HR'). ex_agree HR HR'.
  Qed.

End Segs.

(* [comment removed for export] *)
Definition pixCopy_given_contract2 : Prop :=
  forall C A m md regs (s pixd pixs w h cms datas cmd datad : Z) (cvs cvd : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PCG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs -> pixd <> pixs ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cms datas) -> PIXat m pixd (O23LeptPixCopyT.hdv w h 1 cmd datad) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 1 * h))%Z ->
  live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  O23LeptCloseIface.pcg_cm C A m cms cvs -> O23LeptCloseIface.pcg_cm C A m cmd cvd ->
  (cmd <> 0%Z -> live (c_A0 C) (Z_to_bv 64 cmd) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cvd)) = None) ->
  (* [comment removed for export] *) datas <> datad -> datad <> pixd ->
  (* [comment removed for export] *) (cmd <> 0%Z -> c_arr cvd <> pixd /\ c_arr cvd <> pixs /\ c_arr cvd <> datad /\ c_arr cvd <> datas /\ cmd <> datad /\ cmd <> datas /\
                          (cms <> 0%Z -> cmd <> cms /\ c_arr cvd <> c_arr cvs)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmapcopy <= kR)%Z -> (RB_cmapT cms <= bR)%Z ->
  (forall A' m' vm' regs' (cmd' : Z) (cvd' : cmapv),
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 pixd ->
     FRM C s m m' ->
     (forall (q : word) k i, live A q = Some k -> q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 datad ->
                             q <> Z_to_bv 64 cmd -> q <> Z_to_bv 64 (c_arr cvd) -> (0 <= i < k)%Z -> m' (at_ q i) = m (at_ q i)) ->
     (forall (q : word) k, live A q = Some k -> (cmd <> 0%Z -> q <> Z_to_bv 64 cmd /\ q <> Z_to_bv 64 (c_arr cvd)) -> live A' q = Some k) ->
     PIXat m' pixd (O23LeptPixCopyT.hdv w h 1 cmd' datad) ->
     O23LeptPixCopyGC.pcg_live C A A' m' cms cvs cmd (c_arr cvd) cmd' cvd' ->
     aroom A' vm' (kR - RK_cmapcopy) (bR - RB_cmapT cms) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6eb5c : word) m al_rom) md) S.

(* [comment removed for export] *)

Ltac pcggW_pc RUN :=
  lazymatch type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with pc by (apply bv_eq; reflexivity) end end.

Ltac pcggW_run HW RUN :=
  pcggW_pc RUN;
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].

Lemma pcggW_at : forall C A m md (q : word) (k i : Z), Cok C -> W C A m md -> live A q = Some k -> (0 <= i < k)%Z ->
  u (at_ q i) = (u q + i)%Z /\ (4096 <= u q)%Z /\ (u q + k <= alloc_top (c_vm C))%Z.
Proof.
  intros C A m md q k i CK HW L Hi.
  destruct (blk_range C A m md q k CK HW L ltac:(lia)) as [G T].
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  unfold at_. rewrite u_Z2bv by lia. lia.
Qed.

Theorem pixCopy_given_W : pixCopy_given_contract2.
Proof.
  intros C A m md regs s pixd pixs w h cms datas cmd datad cvs cvd ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 NEds PXs PXd HOK Hw Hh
    Lps Lds Lpd Ldd Lpd0 Ldd0 CMs CMd CMd0 NEsd NEdp NEc kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold PCG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w 1 ltac:(lia) DV) as Hwpl.
  assert (Hn : (0 < 4 * (wpl_of w 1 * h) < 2 ^ 31)%Z) by (split; [nia | lia]).
  assert (Hn0 : (0 <= wpl_of w 1 * h)%Z) by nia.
  pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof PXd as (Hd0 & Hd64' & WFd & _).
  pose proof (wf_data _ WFs) as Rds. pose proof (wf_data _ WFd) as Rdd. cbn [p_data O23LeptPixCopyT.hdv] in Rds, Rdd.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pixd) 64 CK HW Lpd ltac:(lia)) as [Gpd TOPpd]. rewrite u_Z2bv in Gpd, TOPpd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datas) _ CK HW Lds ltac:(lia)) as [Gds TOPds]. rewrite u_Z2bv in Gds, TOPds by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datad) _ CK HW Ldd ltac:(lia)) as [Gdd TOPdd]. rewrite u_Z2bv in Gdd, TOPdd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpd) as (_ & ALpd & _). rewrite u_Z2bv in ALpd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lds) as (_ & ALds & _). rewrite u_Z2bv in ALds by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ldd) as (_ & ALdd & _). rewrite u_Z2bv in ALdd by lia.
  assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (apply O23LeptPixCopyT.zbv_ne2; lia).
  assert (NEpdd : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (apply O23LeptPixCopyT.zbv_ne2; lia).
  assert (NEsdd : Z_to_bv 64 datas <> Z_to_bv 64 datad) by (apply O23LeptPixCopyT.zbv_ne2; lia).
  pose proof (blk_apart C A m md _ _ _ _ CK HW Lps Lpd NEsp ltac:(lia) ltac:(lia)) as APsd. rewrite !u_Z2bv in APsd by lia.
  pose proof (blk_apart C A m md _ _ _ _ CK HW Lpd Ldd NEpdd ltac:(lia) ltac:(lia)) as APpdd. rewrite !u_Z2bv in APpdd by lia.
  pose proof (blk_apart C A m md _ _ _ _ CK HW Lds Ldd NEsdd ltac:(lia) ltac:(lia)) as APsdd. rewrite !u_Z2bv in APsdd by lia.
  apply O23LeptCmap2.box_i in APsd. apply O23LeptCmap2.box_i in APpdd. apply O23LeptCmap2.box_i in APsdd.
  assert (NXd : cmd <> 0%Z -> Z_to_bv 64 pixd <> Z_to_bv 64 cmd /\ Z_to_bv 64 pixd <> Z_to_bv 64 (c_arr cvd)).
  { intros NZ. destruct CMd as [CM0 | (_ & CM & _ & Lcm & _)]; [contradiction|]. destruct (NEc NZ) as (N1 & _).
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF) as Ra.
    split; [intros E; rewrite E in Lpd; rewrite Lpd in Lcm; discriminate | apply O23LeptPixCopyT.zbv_ne2; lia]. }
  assert (NXs : cmd <> 0%Z -> Z_to_bv 64 pixs <> Z_to_bv 64 cmd /\ Z_to_bv 64 pixs <> Z_to_bv 64 (c_arr cvd)).
  { intros NZ. destruct CMd as [CM0 | (_ & CM & _ & Lcm & _)]; [contradiction|]. destruct (NEc NZ) as (_ & N2 & _).
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF) as Ra.
    split; [intros E; rewrite E in Lps; rewrite Lps in Lcm; discriminate | apply O23LeptPixCopyT.zbv_ne2; lia]. }
  assert (NXdd : cmd <> 0%Z -> Z_to_bv 64 datad <> Z_to_bv 64 cmd /\ Z_to_bv 64 datad <> Z_to_bv 64 (c_arr cvd)).
  { intros NZ. destruct CMd as [CM0 | (_ & CM & _ & Lcm & _)]; [contradiction|]. destruct (NEc NZ) as (_ & _ & N3 & _ & N5 & _).
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF) as Ra.
    split; apply O23LeptPixCopyT.zbv_ne2; lia. }
  assert (NXds : cmd <> 0%Z -> Z_to_bv 64 datas <> Z_to_bv 64 cmd /\ Z_to_bv 64 datas <> Z_to_bv 64 (c_arr cvd)).
  { intros NZ. destruct CMd as [CM0 | (_ & CM & _ & Lcm & _)]; [contradiction|]. destruct (NEc NZ) as (_ & _ & _ & N4 & _ & N6 & _).
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF) as Ra.
    split; apply O23LeptPixCopyT.zbv_ne2; lia. }
  assert (HCd0 : cmd = 0%Z \/ (CMAPat m cmd cvd /\ O23LeptCmapValid.cmap_ok cvd /\ live A (Z_to_bv 64 cmd) = Some 24%Z /\
                    live A (Z_to_bv 64 (c_arr cvd)) = Some (4 * c_nalloc cvd)%Z /\
                    live (c_A0 C) (Z_to_bv 64 cmd) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cvd)) = None /\
                    c_arr cvd <> pixd /\ c_arr cvd <> pixs /\ (cms <> 0%Z -> cmd <> cms /\ c_arr cvd <> c_arr cvs))).
  { destruct CMd as [CM0 | (NZ & CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
    destruct (CMd0 NZ) as [L0c L0a]. destruct (NEc NZ) as (N1 & N2 & _ & _ & _ & _ & N7).
    exact (conj CM (conj CMOK (conj Lcm (conj Larr (conj L0c (conj L0a (conj N1 (conj N2 N7)))))))). }
  apply O23LeptCmap2.box_i in NEc. apply O23LeptCmap2.box_i in CMd0. apply O23LeptCmap2.box_i in HCd0.
  apply O23LeptCmap2.box_i in NXd. apply O23LeptCmap2.box_i in NXs. apply O23LeptCmap2.box_i in NXdd. apply O23LeptCmap2.box_i in NXds.
  apply O23LeptCmap2.box_i in NEsd. apply O23LeptCmap2.box_i in NEdp.
  destruct (pcg_A al_rom regs m s pixd pixs (O23LeptPixCopyT.hdv w h 1 cms datas) ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NEds (al16_mod8 _ ALps) PXs
              ltac:(lia) Hn Hn0 (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & Q18 & AG1).
  cbn [p_wpl p_h O23LeptPixCopyT.hdv] in Q18.
  pcggW_run HW RUN1.
  assert (WP1 : W C A (O23LeptCmap2.FR5 m s ret regs) md /\ POSTM C A s m (O23LeptCmap2.FR5 m s ret regs)) by (unfold O23LeptCmap2.FR5; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := O23LeptCmap2.FR5 m s ret regs) in *.
  pose proof (cells5_FR5 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 48 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold O23LeptCmap2.FR5. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (OUT2 : forall x : word, (u x < s - 48 - 72)%Z -> O23LeptPma1G.FR9 M1 (s - 48) (getr r1 1) r1 x = m x).
  { intros x Hx. rewrite O23LeptPma1G.FR9_out by lia. apply OUT1. lia. }
  assert (PXd2 : PIXat (O23LeptPma1G.FR9 M1 (s - 48) (getr r1 1) r1) pixd (O23LeptPixCopyT.hdv w h 1 cmd datad))
    by (apply (PIXat_frame m); [exact PXd | intros x Hx; apply OUT2; lia]).
  assert (PXs2 : PIXat (O23LeptPma1G.FR9 M1 (s - 48) (getr r1 1) r1) pixs (O23LeptPixCopyT.hdv w h 1 cms datas))
    by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT2; lia]).
  destruct (prd_eq_run al_rom r1 M1 (s - 48) pixd pixs (O23LeptPixCopyT.hdv w h 1 cmd datad) (O23LeptPixCopyT.hdv w h 1 cms datas) (getr r1 1)
              ltac:(lia) ltac:(lia) ltac:(rewrite Q1; red; apply bv_eq; reflexivity) ltac:(lia) ltac:(lia) NEds (al16_mod8 _ ALpd) (al16_mod8 _ ALps)
              PXd2 PXs2 eq_refl eq_refl eq_refl (W_sok_win C A M1 md (s - 48 - 80) 80 CK HW1 ltac:(lia) ltac:(cbn; lia)) Q2 eq_refl Q10 Q11)
    as (r2 & RUN2 & U2 & U1 & U10 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & U23 & AG2).
  pcggW_run HW1 RUN2.
  destruct (FR9_WP C A M1 md (s - 48) s (getr r1 1) r1 CK HW1 ltac:(lia) ltac:(lia) Hhi) as [HW2 PM2].
  set (M2 := O23LeptPma1G.FR9 M1 (s - 48) (getr r1 1) r1) in *.
  assert (CE2 : cells5 M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out M1 M2 (s - 48 - 72) (s - 48) s); [intros x Hx; subst M2; apply O23LeptPma1G.FR9_out; lia | lia | lia | lia | exact CE1]. }
  pose proof (proj2 (POSTM_trans C A s m M1 M2 PM1 PM2)) as LV2.
  destruct (pcg_B al_rom r2 M2 pixd pixs U10 (eq_trans U8 Q8) (eq_trans U9 Q9)) as (r3 & RUN3 & P1 & P10 & P11 & AG3).
  rewrite Q1. pcggW_run HW2 RUN3.
  assert (HCs : cms = 0%Z \/ (CMAPat M2 cms cvs /\ O23LeptCmapValid.cmap_ok cvs /\ live A (Z_to_bv 64 cms) = Some 24%Z /\
                                live A (Z_to_bv 64 (c_arr cvs)) = Some (4 * c_nalloc cvs)%Z)).
  { destruct CMs as [CM0 | (_ & CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
    split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cms) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm].
    rewrite u_Z2bv in Gcm, TOPcm by lia. apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT2. lia. }
  assert (HCd : cmd = 0%Z \/ (CMAPat M2 cmd cvd /\ O23LeptCmapValid.cmap_ok cvd /\ live A (Z_to_bv 64 cmd) = Some 24%Z /\
                    live A (Z_to_bv 64 (c_arr cvd)) = Some (4 * c_nalloc cvd)%Z /\
                    live (c_A0 C) (Z_to_bv 64 cmd) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cvd)) = None /\
                    c_arr cvd <> pixd /\ c_arr cvd <> pixs /\ (cms <> 0%Z -> cmd <> cms /\ c_arr cvd <> c_arr cvs))).
  { destruct (O23LeptCmap2.box_e _ HCd0) as [CM0 | (CM & REST)]; [left; exact CM0 | right]. split; [| exact REST].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cmd) 24 CK HW (proj1 (proj2 REST)) ltac:(lia)) as [Gcm TOPcm].
    rewrite u_Z2bv in Gcm, TOPcm by lia. apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT2. lia. }
  apply (pixCopyColormap_given_W C A M2 md r3 (s - 48) pixd pixs (O23LeptPixCopyT.hdv w h 1 cmd datad) (O23LeptPixCopyT.hdv w h 1 cms datas) cvs cvd (getr r3 1) S
           CK HW2 ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
           eq_refl ltac:(rewrite P1; red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) P10 P11 PXd2 PXs2 eq_refl NEds Lpd Lpd0 Lps HCs HCd kR bR Hrm Hrk Hrb).
  intros A4 M4 vm4 r4 cd4 cvd4 HW4 CS4 PM4 KP4 PXd4 PXs4 LV4 PL4 Hrm4.
  clear HCs HCd.
  change (set_cmap (O23LeptPixCopyT.hdv w h 1 cmd datad) cd4) with (O23LeptPixCopyT.hdv w h 1 cd4 datad) in PXd4.
  rewrite P1.
  pose proof (LV4 _ _ Lpd (O23LeptCmap2.box_e _ NXd)) as Lpd4. pose proof (LV4 _ _ Lps (O23LeptCmap2.box_e _ NXs)) as Lps4.
  pose proof (LV4 _ _ Ldd (O23LeptCmap2.box_e _ NXdd)) as Ldd4. pose proof (LV4 _ _ Lds (O23LeptCmap2.box_e _ NXds)) as Lds4.
  destruct (pcg_C al_rom r4 M4 s pixs pixd (O23LeptPixCopyT.hdv w h 1 cms datas) (O23LeptPixCopyT.hdv w h 1 cd4 datad)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (al16_mod8 _ ALpd) PXs4 PXd4
              ltac:(pose proof (spp_of_range 1); cbn [p_spp O23LeptPixCopyT.hdv]; lia) eq_refl eq_refl eq_refl eq_refl eq_refl
              (O23LeptCmap2.box_e _ APsd) ltac:(lia) ltac:(lia)
              (blk_sok C A4 M4 _ pixd 64 CK HW4 Lpd4 ltac:(lia) ltac:(lia) ltac:(lia)) (W_sok_win C A4 M4 _ (s - 80) 32 CK HW4 ltac:(lia) ltac:(cbn; lia))
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r5 & RUN5 & V2 & V8 & V9 & AG5).
  pcggW_run HW4 RUN5.
  change (p_spp (O23LeptPixCopyT.hdv w h 1 cms datas)) with (spp_of 1).
  set (M5 := PCGM M4 s pixd pixs (spp_of 1)) in *.
  assert (WP5 : W C A4 M5 (with_vmmaps vm4 md) /\ POSTM C (c_A0 C) (s - 48) M4 M5).
  { subst M5. unfold PCGM.
    repeat first
      [ apply (WP_blk C (c_A0 C) A4 M4 _ _ (Z_to_bv 64 pixd) _ 64);
          [exact CK | | exact Lpd4 | exact Lpd0 | exact Lpd0 | exact (W_sub0 _ _ _ _ HW4)
          | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]
      | apply (WP_win C A4 (c_A0 C) M4 _ _ _ _ (s - 48) CK);
          [| exact (W_sub0 _ _ _ _ HW4) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia] ].
    split; [exact HW4 | apply POSTM_refl]. }
  destruct WP5 as [HW5 PM5].
  assert (OUT5 : forall x : word, ~ (pixd + 12 <= u x < pixd + 48)%Z -> ~ (s - 72 <= u x < s - 48)%Z -> M5 x = M4 x).
  { intros x Hx1 Hx2. subst M5. unfold PCGM. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXd5 : PIXat M5 pixd (O23LeptPixCopyT.hdv w h 1 cd4 datad)).
  { subst M5. unfold PCGM.
    apply O23LeptPixCopyT.PIX_wr_text0; [| reflexivity].
    do 3 (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
    apply O23LeptPixCopyT.PIX_wr_fmt0; [| reflexivity].
    apply O23LeptPixCopyT.PIX_wr_res0; [| reflexivity | reflexivity].
    exact (O23LeptPixCopyT.PIX_wr_spp_same M4 pixd _ PXd4). }
  assert (PXs5 : PIXat M5 pixs (O23LeptPixCopyT.hdv w h 1 cms datas)).
  { pose proof (O23LeptCmap2.box_e _ APsd) as U. apply (PIXat_frame M4); [exact PXs4|]. intros x Hx. apply OUT5; lia. }
  pose proof (cells5_frm C (s - 48) M2 M5 s _ _ _ _ _ CK (proj1 (POSTM_trans _ _ _ _ _ _ PM4 PM5)) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE5.
  destruct (pcg_D al_rom r5 M5 s pixd pixs (O23LeptPixCopyT.hdv w h 1 cd4 datad) (O23LeptPixCopyT.hdv w h 1 cms datas) (4 * (wpl_of w 1 * h))
              ltac:(lia) (al16_mod4 _ ALdd) (al16_mod4 _ ALds) ltac:(lia) ltac:(lia) PXd5 PXs5 V2 V8 V9 ltac:(csr; reflexivity))
    as (r6 & RUN6 & Y2 & Y1 & Y10 & Y11 & Y12 & Y8 & Y9 & Y18 & AG6).
  pcggW_run HW5 RUN6.
  destruct (blk_rdn C A4 M5 _ datas (4 * (wpl_of w 1 * h)) (Z.to_nat (4 * (wpl_of w 1 * h))) CK HW5 Lds4 ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Hsrc & Hlen).
  assert (HOKm : mcH M5 (Z_to_bv 64 datad) (Z_to_bv 64 datas) (4 * (wpl_of w 1 * h)) bs).
  { pose proof (O23LeptCmap2.box_e _ APsdd) as U.
    constructor; rewrite ?u_Z2bv by lia;
      [lia | exact Hlen | rewrite Hlen; exact Hsrc | rewrite Hlen; exact (blk_sok C A4 M5 _ datad _ CK HW5 Ldd4 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | lia]. }
  destruct (ref_memcpy M5 _ _ _ bs al_rom HOKm r6 (getr r6 1) ltac:(rewrite Y1; red; apply bv_eq; reflexivity) eq_refl Y10 Y11 Y12) as (r7 & RUN7 & KP7).
  pcggW_run HW5 RUN7.
  rewrite Y1.
  set (M6 := wbytes M5 (Z_to_bv 64 datad) bs) in *.
  assert (HW6 : W C A4 M6 (with_vmmaps vm4 md)).
  { subst M6. apply (W_store_blk C A4 M5 _ (Z_to_bv 64 datad) (Z_to_bv 64 datad) _ bs CK HW5 Ldd4 Ldd0); rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
  assert (PM6 : POSTM C (c_A0 C) s M5 M6).
  { subst M6. apply (POSTM_blk C (c_A0 C) A4 M5 _ (Z_to_bv 64 datad) (Z_to_bv 64 datad) _ bs s CK HW5 Ldd4 Ldd0 (W_sub0 _ _ _ _ HW5));
      rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
  assert (OUT6 : forall x : word, ~ (datad <= u x < datad + 4 * (wpl_of w 1 * h))%Z -> M6 x = M5 x).
  { intros x Hx. subst M6. apply wbytes_outside; rewrite Hlen, u_Z2bv by lia; lia. }
  assert (CE6 : cells5 M6 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19))
    by (apply (cells5_out M5 M6 datad (datad + 4 * (wpl_of w 1 * h)) s); [exact OUT6 | lia | lia | lia | exact CE5]).
  assert (PXd6 : PIXat M6 pixd (O23LeptPixCopyT.hdv w h 1 cd4 datad)).
  { pose proof (O23LeptCmap2.box_e _ APpdd) as U. apply (PIXat_frame M5); [exact PXd5|]. intros x Hx. apply OUT6. lia. }
  assert (K2 : getr r7 2 = getr r6 2) by (apply KP7; in_kept). assert (K8 : getr r7 8 = getr r6 8) by (apply KP7; in_kept).
  assert (K3 : getr r7 3 = getr r6 3) by (apply KP7; in_kept). assert (K4 : getr r7 4 = getr r6 4) by (apply KP7; in_kept).
  assert (K20 : getr r7 20 = getr r6 20) by (apply KP7; in_kept). assert (K21 : getr r7 21 = getr r6 21) by (apply KP7; in_kept).
  assert (K22 : getr r7 22 = getr r6 22) by (apply KP7; in_kept). assert (K23 : getr r7 23 = getr r6 23) by (apply KP7; in_kept).
  assert (K24 : getr r7 24 = getr r6 24) by (apply KP7; in_kept). assert (K25 : getr r7 25 = getr r6 25) by (apply KP7; in_kept).
  assert (K26 : getr r7 26 = getr r6 26) by (apply KP7; in_kept). assert (K27 : getr r7 27 = getr r6 27) by (apply KP7; in_kept).
  destruct (V23LeptPixCopyST.pcp_D al_rom r7 M6 s pixd ret _ _ _ _ ltac:(lia) ltac:(lia) Hret CE6 ltac:(rewrite K2; exact Y2) ltac:(rewrite K8; exact Y8))
    as (r8 & RUN8 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & Z19 & AG8).
  pcggW_run HW6 RUN8.
  assert (PMall : POSTM C (c_A0 C) s m M6).
  { apply (POSTM_trans C (c_A0 C) s m M5 M6); [| exact PM6].
    apply (POSTM_trans C (c_A0 C) s m M2 M5).
    - apply (POSTM_sub C (c_A0 C) A); [exact (W_sub0 _ _ _ _ HW) | exact (POSTM_trans C A s m M1 M2 PM1 PM2)].
    - apply (POSTM_mono C (c_A0 C) (s - 48) s); [lia | exact (POSTM_trans _ _ _ _ _ _ PM4 PM5)]. }
  apply (HK A4 M6 vm4 r8 cd4 cvd4 HW6).
  - apply cs_kept_intro; csr; reflexivity.
  - exact Z10.
  - exact (proj1 PMall).
  - intros q k i Lq N1 N2 N3 N4 Hi.
    destruct (pcggW_at C A m md q k i CK HW Lq Hi) as (Eu & Gq & Tq).
    pose proof (blk_apart C A m md _ _ _ _ CK HW Lq Lpd N1 ltac:(lia) ltac:(lia)) as D1. rewrite u_Z2bv in D1 by lia.
    pose proof (blk_apart C A m md _ _ _ _ CK HW Lq Ldd N2 ltac:(lia) ltac:(lia)) as D2. rewrite u_Z2bv in D2 by lia.
    rewrite OUT6 by lia. rewrite OUT5 by lia.
    rewrite (KP4 q k i Lq); [exact (LV2 q k i Lq Hi) | | exact Hi].
    intros [X | [_ [X | X]]]; [exact (N1 X) | exact (N3 X) | exact (N4 X)].
  - exact LV4.
  - exact PXd6.
  - destruct PL4 as [PL | (NZs & NZd & CDat & CDok & Ec1 & Ec2 & Ec3 & Lcd & Lca & L0cd & L0ca & SEP & LEQ & LNONE)]; [left; exact PL | right].
    destruct (SEP _ _ Lpd (O23LeptCmap2.box_e _ NXd)) as [Spd _]. destruct (SEP _ _ Ldd (O23LeptCmap2.box_e _ NXdd)) as [Sdd _].
    pose proof CDat as (Hcd0 & Hcd64 & _).
    destruct (blk_range C A4 M4 _ (Z_to_bv 64 cd4) 24 CK HW4 Lcd ltac:(lia)) as [Gcd TOPcd]. rewrite u_Z2bv in Gcd, TOPcd by lia.
    pose proof (blk_apart C A4 M4 _ _ _ _ _ CK HW4 Lcd Lpd4 (not_eq_sym Spd) ltac:(lia) ltac:(lia)) as D1. rewrite !u_Z2bv in D1 by lia.
    pose proof (blk_apart C A4 M4 _ _ _ _ _ CK HW4 Lcd Ldd4 (not_eq_sym Sdd) ltac:(lia) ltac:(lia)) as D2. rewrite !u_Z2bv in D2 by lia.
    refine (conj NZs (conj NZd (conj _ (conj CDok (conj Ec1 (conj Ec2 (conj Ec3 (conj Lcd (conj Lca (conj L0cd (conj L0ca (conj SEP (conj LEQ LNONE))))))))))))).
    apply (CMAPat_frame M4); [exact CDat|]. intros x Hx. rewrite OUT6 by lia. apply OUT5; lia.
  - exact Hrm4.
Qed.

End PixCopyG.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
