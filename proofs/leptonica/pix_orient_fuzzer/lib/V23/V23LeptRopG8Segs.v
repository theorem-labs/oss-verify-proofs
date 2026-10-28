(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith GrayLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb V23LeptRop2Segs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_rasteropLow_85000_86000 V23_code_rasteropLow_87000_875f4.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.


Definition RG8_S1 : word := 0x85b70.
Definition RG8_F : word := 0x85bfc.
Definition RG8_X1 : word := 0x85ce8.
Definition RG8_H2 : word := 0x85d38.
Definition RG8_I : word := 0x85d5c.
Definition RG8_T2 : word := 0x85df4.
Definition RG8_X2 : word := 0x85e64.
Definition RG8_L : word := 0x85f00.
Definition RG8_JT : Z := (RG_JT + 4 * (8 - 1))%Z.
Definition RG8_JTV : Z := 419800.

Section Segs8G.
Context {fx : FPState}.
Variable rom : word -> option byte.

Lemma g8g8a_add : forall a b : Z, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b. rewrite <- alu_add. apply ex_ptr_val. Qed.

Lemma g8g8a_addw : forall a b : Z, (- 2 ^ 31 <= a + b < 2 ^ 31)%Z -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b H. rewrite v_addw_Z, (sw32_small (a + b)) by lia. reflexivity. Qed.

Lemma g8g8a_subw : forall a b : Z, (- 2 ^ 31 <= a - b < 2 ^ 31)%Z -> v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H. rewrite v_subw_Z, (sw32_small (a - b)) by lia. reflexivity. Qed.

Lemma g8g8a_sra_srai : forall w : word, v_sra w (Z_to_bv 64 63) = v_srai w 63.
Proof. intros w. unfold v_sra, v_srai. rewrite (u_Z2bv 63) by lia. reflexivity. Qed.

Lemma g8g8a_min63 : forall x : Z, (- 2 ^ 63 <= x < 2 ^ 63)%Z ->
  v_and (v_sra (Z_to_bv 64 x) (Z_to_bv 64 63)) (Z_to_bv 64 x) = Z_to_bv 64 (Z.min 0 x).
Proof. intros x Hx. rewrite g8g8a_sra_srai. apply and_srai63_min. exact Hx. Qed.

Lemma g8g8a_slt0 : forall a : Z, (0 <= a < 2 ^ 63)%Z -> v_slt (Z_to_bv 64 a) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof.
  intros a Ha. unfold v_slt, c_lts, bv_lts. rewrite !bv_signed_Zs by lia.
  replace (a <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma g8g8a_and1 : forall a : Z, (0 <= a <= 1)%Z -> v_and (Z_to_bv 64 a) (Z_to_bv 64 1) = Z_to_bv 64 a.
Proof. intros a Ha. assert (a = 0 \/ a = 1)%Z as [-> | ->] by lia; apply bv_eq; reflexivity. Qed.

Lemma g8g8a_xor0l : forall b : Z, (0 <= b < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 0) (Z_to_bv 64 b) = Z_to_bv 64 b.
Proof. intros b Hb. unfold v_xor. rewrite !u_Z2bv by lia. rewrite Z.lxor_0_l. reflexivity. Qed.

Lemma g8g8a_bne : forall x y : Z, (- 2 ^ 63 <= x < 2 ^ 63)%Z -> (- 2 ^ 63 <= y < 2 ^ 63)%Z -> x <> y ->
  Sem.branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof.
  intros x y Hx Hy Hxy. cbn [Sem.branch_taken]. destruct (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) eqn:E; [exfalso | reflexivity].
  unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. apply (f_equal bv_signed) in E.
  rewrite !bv_signed_Zs in E by lia. exact (Hxy E).
Qed.

Ltac g8g8a_norm :=
  rewrite ?w_mulw, ?m_mul;
  repeat first [ rewrite g8g8a_min63 by lia | rewrite zbv_snez by lia | rewrite zbv_sltu_ge by lia | rewrite g8g8a_xor0l by lia
               | rewrite g8g8a_slt0 by lia | rewrite g8g8a_and1 by lia | rewrite zbv_mul | rewrite g8g8a_add
               | rewrite g8g8a_subw by lia | rewrite g8g8a_addw by lia ].

Ltac g8g8a_fin := ex_vnorm; g8g8a_norm; first [reflexivity | f_equal; lia].

Ltac g8g8a_sc := ex_vnorm; g8g8a_norm; first [ex_br | apply g8g8a_bne; lia].

Ltac g8g8a_at H :=
  match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
    match type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
      replace a with a' by (rewrite ?Z.add_0_r; first [reflexivity | lia]); exact H end end.

Ltac g8g8a_rd :=
  match goal with H : rdn _ _ (Z_to_bv 64 _) _ = Some ?bs |- exists _, _ =>
    exists bs; split; [g8g8a_at H | reflexivity] end.

(* [comment removed for export] *)
Lemma rg8_S1 : forall (fw f6 f7 : bool) regs m (s dxb psf pdf swpl dwpl dh : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= dxb < 32)%Z -> (if fw then dxb <> 0 else dxb = 0)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  getr regs 1 = Z_to_bv 64 dxb -> getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 8 = true ->
  (fw = true ->
     (0 <= psf < 2 ^ 64)%Z /\ (0 <= pdf < 2 ^ 64)%Z /\ (psf mod 4 = 0)%Z /\ (pdf mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
     getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0) /\
     rdn SEGS m (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0))) /\
     rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
     rg_rows m s dh) ->
  exists regs',
    msteps SEGS (mkst regs RG8_S1 m rom)
                (mkst regs' (if fw then RG8_F else RG8_X1)
                      (if fw then wbytes m (Z_to_bv 64 (s - 240)) (word_to_le_bytes 8 (v_xor (getr regs 31) (Z_to_bv 64 (-1)))) else m) rom)
    /\ (fw = true -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 (psf + 4 * swpl) /\ getr regs' 27 = Z_to_bv 64 (4 * swpl)
                     /\ getr regs' 7 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 16 = Z_to_bv 64 pdf /\ getr regs' 28 = Z_to_bv 64 (- dh)
                     /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 (if f6 then 1 else 0) /\ getr regs' 24 = Z_to_bv 64 (if f7 then 1 else 0)
                     /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 31
                     /\ getr regs' 22 = Z_to_bv 64 32)
    /\ regs_agree (fun r => In r [1; 5; 7; 9; 11; 12; 13; 16; 17; 19; 20; 22; 23; 24; 27; 28]%list) regs regs'.
Proof.
  intros fw f6 f7 regs m s dxb psf pdf swpl dwpl dh Hs Hs64 Hdxb Hfw Hswpl Hdwpl H1 H2 H14 SOK HF.
  rewrite <- (zbv_self RG8_S1), <- (zbv_self RG8_F), <- (zbv_self RG8_X1).
  destruct fw; cbv iota beta in Hfw |- *.
  2:{ subst dxb. ex_entry regs [s]%Z HR.
      assert (HK : know_ok SEGS (ex_env regs [s]%Z) m [KRange (EVar 32) 240 (2 ^ 64 - 1)]%Z).
      { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
      ex_run 100%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [] [] []) HR HK R' HR' Hms.
      exists R'. split; [ex_mem regs Hms | split; [intros; discriminate | ex_agree HR HR']]. }
  destruct (HF eq_refl) as (Hpsf & Hpdf & ALs & ALd & Hdh & H15 & H25 & H26 & Cf6 & Cswpl & ROWS).
  destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
  assert (F6r : (0 <= (if f6 then 1 else 0) <= 1)%Z) by (destruct f6; lia).
  assert (F7r : (0 <= (if f7 then 1 else 0) <= 1)%Z) by (destruct f7; lia).
  ex_entry regs [s; dxb; psf; pdf; swpl; dwpl; dh; c28; c30; c38; c40; c48; c50; if f6 then 1 else 0; if f7 then 1 else 0]%Z HR.
  assert (HK : know_ok SEGS (ex_env regs [s; dxb; psf; pdf; swpl; dwpl; dh; c28; c30; c38; c40; c48; c50; if f6 then 1 else 0; if f7 then 1 else 0]%Z) m
    [KRange (EVar 32) 240 (2 ^ 64 - 1); KWr (SA (EVar 32) (-240)) 8;
     KRange (EVar 33) 1 31; KRange (EVar 34) 0 (2 ^ 64 - 1); KAlign (EVar 34) 4; KRange (EVar 35) 0 (2 ^ 64 - 1); KAlign (EVar 35) 4;
     KRange (EVar 36) 0 (2 ^ 24 - 1); KRange (EVar 37) 0 (2 ^ 24 - 1); KRange (EVar 38) 1 (2 ^ 24 - 1);
     KRange (EVar 45) 0 1; KRange (EVar 46) 0 1;
     KWord (SA (EVar 32) (-224)) 8 (EVar 45); KWord (SA (EVar 32) (-152)) 8 (EVar 36);
     KWord (SA (EVar 32) (-200)) 8 (EVar 39); KWord (SA (EVar 32) (-192)) 8 (EVar 40); KWord (SA (EVar 32) (-184)) 8 (EVar 41);
     KWord (SA (EVar 32) (-176)) 8 (EVar 42); KWord (SA (EVar 32) (-168)) 8 (EVar 43); KWord (SA (EVar 32) (-160)) 8 (EVar 44)]%Z).
  { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
  ex_run 400%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [true; true; true; true; true; true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms |]. split.
    - intros _. repeat split. all: try (ex_reg regs HR'; g8g8a_fin).
    - ex_agree HR HR'. }
  all: try solve [g8g8a_sc].
Qed.

(* [comment removed for export] *)
Lemma rg8_F : forall (f6 f7 last : bool) regs m (s psf off pd s4 d4 n sls : Z) (nm : word) (bs0 bs1 bd : list byte),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= psf)%Z -> (0 <= off)%Z -> (0 <= s4)%Z -> (0 <= d4)%Z ->
  (1 <= psf + off)%Z -> (psf + off + s4 < 2 ^ 64)%Z -> (psf + off + 4 < 2 ^ 64)%Z -> (1 <= pd)%Z -> (pd + d4 < 2 ^ 64)%Z -> (pd + 4 < 2 ^ 64)%Z ->
  (pd + 4 <= s - 240 \/ s <= pd)%Z ->
  (1 <= n < 2 ^ 31)%Z -> (if last then n = 1 else 1 < n)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psf + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  (f6 = true -> f7 = false -> psf + off + 8 < 2 ^ 64 /\ rdn SEGS m (Z_to_bv 64 (psf + off + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> length bd = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 240)) 8 = Some (word_to_le_bytes 8 nm) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 15 = Z_to_bv 64 psf -> getr regs 11 = Z_to_bv 64 off ->
  getr regs 25 = Z_to_bv 64 pd -> getr regs 16 = Z_to_bv 64 pd -> getr regs 28 = Z_to_bv 64 (- n) ->
  getr regs 27 = Z_to_bv 64 s4 -> getr regs 7 = Z_to_bv 64 d4 -> getr regs 20 = Z_to_bv 64 (psf + s4) ->
  getr regs 19 = Z_to_bv 64 (if f6 then 1 else 0) -> getr regs 24 = Z_to_bv 64 (if f7 then 1 else 0) ->
  getr regs 13 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 0 -> getr regs 1 = Z_to_bv 64 31 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) -> getr regs 22 = Z_to_bv 64 32 ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG8_F m rom)
                (mkst regs' (if last then RG8_X1 else RG8_F) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (off + s4) /\ getr regs' 25 = Z_to_bv 64 (pd + d4) /\ getr regs' 16 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 28 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [11; 12; 16; 17; 21; 25; 26; 28]%list) regs regs'.
Proof.
  intros f6 f7 last regs m s psf off pd s4 d4 n sls nm bs0 bs1 bd Hs Hs64 Hpsf Hoff Hs4 Hd4 Hps1 Hps2 Hps4 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cz Cnm H2 H15 H11 H25 H16 H28 H27 H7 H20 H19 H24 H13 H23 H9 H1 H30 H8 H22.
  rewrite <- (zbv_self RG8_F), <- (zbv_self RG8_X1).
  assert (R1x : f6 = true -> f7 = false -> rdn SEGS m (Z_to_bv 64 (psf + off + 4)) 4 = Some bs1).
  { intros E6 E7. destruct (R1 E6 E7) as (_ & X & _). exact X. }
  assert (Hps8 : f6 = true -> f7 = false -> (psf + off + 8 < 2 ^ 64)%Z).
  { intros E6 E7. destruct (R1 E6 E7) as (X & _ & _). exact X. }
  clear R1.
  destruct last; cbv iota beta in Hlast |- *; [rewrite Hlast in H28 |].
  all: destruct f6, f7.
  all: try specialize (R1x eq_refl eq_refl).
  all: try specialize (Hps8 eq_refl eq_refl).
  { ex_entry regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 1); KRange (EVar 35) 1 (2 ^ 64 - 1);
       KRange (EVar 37) 0 (2 ^ 64 - 1); KRange (EVar 38) 0 (2 ^ 64 - 1); KRange (EVar 39) 0 (2 ^ 64 - 1);
       KRange (EVar 40) 1 31; KRange (EVar 41) 1 31; KWr (SA (EVar 35) 0) 4;
       KWord (SA (EVar 32) (-120)) 8 (ELit 0); KWord (SA (EVar 32) (-240)) 8 (EVar 42)]%Z)
      by (unfold know_ok; repeat (apply Forall_cons; [ex_know1 regs |]);
          apply Forall_cons; [| apply Forall_nil];
          eapply ex_kword_w; [ex_eden regs | ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply zbv_self
                             | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | replace (s + -240)%Z with (s - 240)%Z by lia; exact Cnm]).
    ex_run 600%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [true; true; true; true; true; true; true; true; true; true; true; true] [EVar 43; EVar 45] []) HR HK R' HR' Hms.
    all: try solve [g8g8a_rd].
    all: try solve [g8g8a_sc].
    all: try (exists R'; eexists; split;
           [ eapply ex_msteps_mem; [exact Hms |]; cbn [mem_denot s_log e_addr e_width e_val];
             apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity]
           | repeat split; [..| ex_agree HR HR']; ex_reg regs HR'; g8g8a_fin ]). }
  { ex_entry regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 1); KRange (EVar 35) 1 (2 ^ 64 - 1);
       KRange (EVar 37) 0 (2 ^ 64 - 1); KRange (EVar 38) 0 (2 ^ 64 - 1); KRange (EVar 39) 0 (2 ^ 64 - 1);
       KRange (EVar 40) 1 31; KRange (EVar 41) 1 31; KWr (SA (EVar 35) 0) 4;
       KWord (SA (EVar 32) (-120)) 8 (ELit 0); KWord (SA (EVar 32) (-240)) 8 (EVar 42)]%Z)
      by (unfold know_ok; repeat (apply Forall_cons; [ex_know1 regs |]);
          apply Forall_cons; [| apply Forall_nil];
          eapply ex_kword_w; [ex_eden regs | ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply zbv_self
                             | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | replace (s + -240)%Z with (s - 240)%Z by lia; exact Cnm]).
    ex_run 600%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [true; true; true; true; true; true; true; true; true; true; true; true] [EVar 43; EVar 44; EVar 45] []) HR HK R' HR' Hms.
    all: try solve [g8g8a_rd].
    all: try solve [g8g8a_sc].
    all: try (exists R'; eexists; split;
           [ eapply ex_msteps_mem; [exact Hms |]; cbn [mem_denot s_log e_addr e_width e_val];
             apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity]
           | repeat split; [..| ex_agree HR HR']; ex_reg regs HR'; g8g8a_fin ]). }
  { ex_entry regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 1); KRange (EVar 35) 1 (2 ^ 64 - 1);
       KRange (EVar 37) 0 (2 ^ 64 - 1); KRange (EVar 38) 0 (2 ^ 64 - 1); KRange (EVar 39) 0 (2 ^ 64 - 1);
       KRange (EVar 40) 1 31; KRange (EVar 41) 1 31; KWr (SA (EVar 35) 0) 4;
       KWord (SA (EVar 32) (-120)) 8 (ELit 0); KWord (SA (EVar 32) (-240)) 8 (EVar 42)]%Z)
      by (unfold know_ok; repeat (apply Forall_cons; [ex_know1 regs |]);
          apply Forall_cons; [| apply Forall_nil];
          eapply ex_kword_w; [ex_eden regs | ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply zbv_self
                             | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | replace (s + -240)%Z with (s - 240)%Z by lia; exact Cnm]).
    ex_run 600%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [true; true; true; true; true; true; true; true; true; true; true; true] [EVar 43; EVar 45] []) HR HK R' HR' Hms.
    all: try solve [g8g8a_rd].
    all: try solve [g8g8a_sc].
    all: try (exists R'; eexists; split;
           [ eapply ex_msteps_mem; [exact Hms |]; cbn [mem_denot s_log e_addr e_width e_val];
             apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity]
           | repeat split; [..| ex_agree HR HR']; ex_reg regs HR'; g8g8a_fin ]). }
  { ex_entry regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 1); KRange (EVar 35) 1 (2 ^ 64 - 1);
       KRange (EVar 37) 0 (2 ^ 64 - 1); KRange (EVar 38) 0 (2 ^ 64 - 1); KRange (EVar 39) 0 (2 ^ 64 - 1);
       KRange (EVar 40) 1 31; KRange (EVar 41) 1 31; KWr (SA (EVar 35) 0) 4;
       KWord (SA (EVar 32) (-120)) 8 (ELit 0); KWord (SA (EVar 32) (-240)) 8 (EVar 42)]%Z)
      by (unfold know_ok; repeat (apply Forall_cons; [ex_know1 regs |]);
          apply Forall_cons; [| apply Forall_nil];
          eapply ex_kword_w; [ex_eden regs | ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply zbv_self
                             | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | replace (s + -240)%Z with (s - 240)%Z by lia; exact Cnm]).
    ex_run 600%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [true; true; true; true; true; true; true; true; true; true; true; true] [EVar 43; EVar 45] []) HR HK R' HR' Hms.
    all: try solve [g8g8a_rd].
    all: try solve [g8g8a_sc].
    all: try (exists R'; eexists; split;
           [ eapply ex_msteps_mem; [exact Hms |]; cbn [mem_denot s_log e_addr e_width e_val];
             apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity]
           | repeat split; [..| ex_agree HR HR']; ex_reg regs HR'; g8g8a_fin ]). }
  { ex_entry regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 1); KRange (EVar 35) 1 (2 ^ 64 - 1);
       KRange (EVar 37) 0 (2 ^ 64 - 1); KRange (EVar 38) 0 (2 ^ 64 - 1); KRange (EVar 39) 0 (2 ^ 64 - 1);
       KRange (EVar 40) 1 31; KRange (EVar 41) 1 31; KWr (SA (EVar 35) 0) 4;
       KWord (SA (EVar 32) (-120)) 8 (ELit 0); KWord (SA (EVar 32) (-240)) 8 (EVar 42)]%Z)
      by (unfold know_ok; repeat (apply Forall_cons; [ex_know1 regs |]);
          apply Forall_cons; [| apply Forall_nil];
          eapply ex_kword_w; [ex_eden regs | ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply zbv_self
                             | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | replace (s + -240)%Z with (s - 240)%Z by lia; exact Cnm]).
    ex_run 600%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [true; true; true; true; true; true; true; true; true; true; true; true] [EVar 43; EVar 45] []) HR HK R' HR' Hms.
    all: try solve [g8g8a_rd].
    all: try solve [g8g8a_sc].
    all: try (exists R'; eexists; split;
           [ eapply ex_msteps_mem; [exact Hms |]; cbn [mem_denot s_log e_addr e_width e_val];
             apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity]
           | repeat split; [..| ex_agree HR HR']; ex_reg regs HR'; g8g8a_fin ]). }
  { ex_entry regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 1); KRange (EVar 35) 1 (2 ^ 64 - 1);
       KRange (EVar 37) 0 (2 ^ 64 - 1); KRange (EVar 38) 0 (2 ^ 64 - 1); KRange (EVar 39) 0 (2 ^ 64 - 1);
       KRange (EVar 40) 1 31; KRange (EVar 41) 1 31; KWr (SA (EVar 35) 0) 4;
       KWord (SA (EVar 32) (-120)) 8 (ELit 0); KWord (SA (EVar 32) (-240)) 8 (EVar 42)]%Z)
      by (unfold know_ok; repeat (apply Forall_cons; [ex_know1 regs |]);
          apply Forall_cons; [| apply Forall_nil];
          eapply ex_kword_w; [ex_eden regs | ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply zbv_self
                             | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | replace (s + -240)%Z with (s - 240)%Z by lia; exact Cnm]).
    ex_run 600%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [true; true; true; true; true; true; true; true; true; true; true; true] [EVar 43; EVar 44; EVar 45] []) HR HK R' HR' Hms.
    all: try solve [g8g8a_rd].
    all: try solve [g8g8a_sc].
    all: try (exists R'; eexists; split;
           [ eapply ex_msteps_mem; [exact Hms |]; cbn [mem_denot s_log e_addr e_width e_val];
             apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity]
           | repeat split; [..| ex_agree HR HR']; ex_reg regs HR'; g8g8a_fin ]). }
  { ex_entry regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 1); KRange (EVar 35) 1 (2 ^ 64 - 1);
       KRange (EVar 37) 0 (2 ^ 64 - 1); KRange (EVar 38) 0 (2 ^ 64 - 1); KRange (EVar 39) 0 (2 ^ 64 - 1);
       KRange (EVar 40) 1 31; KRange (EVar 41) 1 31; KWr (SA (EVar 35) 0) 4;
       KWord (SA (EVar 32) (-120)) 8 (ELit 0); KWord (SA (EVar 32) (-240)) 8 (EVar 42)]%Z)
      by (unfold know_ok; repeat (apply Forall_cons; [ex_know1 regs |]);
          apply Forall_cons; [| apply Forall_nil];
          eapply ex_kword_w; [ex_eden regs | ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply zbv_self
                             | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | replace (s + -240)%Z with (s - 240)%Z by lia; exact Cnm]).
    ex_run 600%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [true; true; true; true; true; true; true; true; true; true; true; true] [EVar 43; EVar 45] []) HR HK R' HR' Hms.
    all: try solve [g8g8a_rd].
    all: try solve [g8g8a_sc].
    all: try (exists R'; eexists; split;
           [ eapply ex_msteps_mem; [exact Hms |]; cbn [mem_denot s_log e_addr e_width e_val];
             apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity]
           | repeat split; [..| ex_agree HR HR']; ex_reg regs HR'; g8g8a_fin ]). }
  { ex_entry regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; psf; off; pd; - n; s4; d4; psf + s4; sls; 32 - sls; bv_unsigned nm;
                   extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 1); KRange (EVar 35) 1 (2 ^ 64 - 1);
       KRange (EVar 37) 0 (2 ^ 64 - 1); KRange (EVar 38) 0 (2 ^ 64 - 1); KRange (EVar 39) 0 (2 ^ 64 - 1);
       KRange (EVar 40) 1 31; KRange (EVar 41) 1 31; KWr (SA (EVar 35) 0) 4;
       KWord (SA (EVar 32) (-120)) 8 (ELit 0); KWord (SA (EVar 32) (-240)) 8 (EVar 42)]%Z)
      by (unfold know_ok; repeat (apply Forall_cons; [ex_know1 regs |]);
          apply Forall_cons; [| apply Forall_nil];
          eapply ex_kword_w; [ex_eden regs | ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply zbv_self
                             | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | replace (s + -240)%Z with (s - 240)%Z by lia; exact Cnm]).
    ex_run 600%nat [bv_unsigned RG8_F; bv_unsigned RG8_X1]%Z (SCR [true; true; true; true; true; true; true; true; true; true; true; true] [EVar 43; EVar 45] []) HR HK R' HR' Hms.
    all: try solve [g8g8a_rd].
    all: try solve [g8g8a_sc].
    all: try (exists R'; eexists; split;
           [ eapply ex_msteps_mem; [exact Hms |]; cbn [mem_denot s_log e_addr e_width e_val];
             apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs | reflexivity]
           | repeat split; [..| ex_agree HR HR']; ex_reg regs HR'; g8g8a_fin ]). }
Qed.

Import SX2. Import SX2S.

Lemma g8b_slt0 : forall a : Z, (0 <= a < 2 ^ 63)%Z -> v_slt (Z_to_bv 64 a) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof.
  intros a Ha. unfold v_slt, c_lts, bv_lts.
  rewrite !GrayLib.bv_signed_Zs by lia.
  destruct (Z.ltb_spec a 0); [lia | reflexivity].
Qed.

Lemma g8b_xor : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold v_xor. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma g8b_and : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> v_and (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.land a b).
Proof. intros a b Ha Hb. unfold v_and. rewrite !u_Z2bv by lia. reflexivity. Qed.

Ltac g8b_sc :=
  rewrite ?w_addw, ?ex_ptr_val, ?alu_add, ?alu_sltu, ?alu_slt, ?alu_and, ?alu_xor, ?m_mul;
  repeat first
    [ rewrite zbv_mul
    | rewrite zbv_addi
    | rewrite v_addw_Z
    | rewrite sw32_small by lia
    | rewrite zbv_snez by lia
    | rewrite zbv_sltu_ge by lia
    | rewrite g8b_slt0 by lia
    | rewrite g8b_xor by lia
    | rewrite g8b_and by lia
    | rewrite Z.lxor_0_l
    | rewrite Z.lxor_0_r
    | rewrite Z.land_diag ].

Ltac g8b_at H :=
  match goal with |- context [Z_to_bv 64 ?a] =>
    match type of H with context [Z_to_bv 64 ?a'] =>
      replace a with a' by (rewrite ?Z.add_0_r; first [reflexivity | lia]); exact H end end.

Ltac g8b_sc2 :=
  first
    [ solve [lazymatch goal with |- exists _, _ =>
               match goal with H : rdn _ _ _ 4 = Some ?bs |- _ =>
                 exists bs; split; [g8b_sc; g8b_at H | reflexivity] end end]
    | solve [lazymatch goal with |- store_ok _ _ _ _ = true =>
               g8b_sc; match goal with H : store_ok _ _ _ _ = true |- _ => g8b_at H end end]
    | solve [lazymatch goal with |- Sem.branch_taken _ _ _ = _ => g8b_sc; ex_br end]
    | solve [g8b_sc; rewrite ?u_Z2bv by lia; repeat split; lia] ].

Ltac g8b_reg regs HR' :=
  lazymatch goal with
  | |- getr _ ?k = _ =>
      rewrite (reg_val _ _ _ k HR');
      match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
      ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
      repeat match goal with H : getr regs _ = _ |- _ => rewrite H end;
      g8b_sc; first [reflexivity | (f_equal; lia)]
  end.

Ltac g8b_addr regs :=
  ex_unfoldE; unfold adenot; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  g8b_sc; rewrite ?Z.add_0_r; first [reflexivity | (f_equal; lia)].


(* [comment removed for export] *)
Lemma rg8_H2 : forall regs m (s nfw psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= nfw < 2 ^ 26)%Z -> (1 <= psrow < 2 ^ 64)%Z -> (1 <= pdrow < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)) ->
  rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  rdn SEGS m (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 18 = Z_to_bv 64 pdrow ->
  exists regs',
    msteps SEGS (mkst regs RG8_H2 m rom) (mkst regs' RG8_I m rom)
    /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 28 = Z_to_bv 64 1
    /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 21 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [9; 12; 16; 19; 21; 28]%list) regs regs'.
Proof.
  intros regs m s nfw psrow pdrow Hs Hs64 Hnfw Hps Hpd Cnfw C208 C224 H2 H6 H18.
  replace RG8_H2 with (Z_to_bv 64 0x85d38) by (apply bv_eq; reflexivity).
  replace RG8_I with (Z_to_bv 64 0x85d5c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; nfw; psrow; pdrow]%Z HR.
  assert (HK : know_ok SEGS (ex_env regs [s; nfw; psrow; pdrow]%Z) m
    [KRange (EVar 32) 240 (2 ^ 64 - 1); KWord (SA (EVar 32) (-128)) 8 (EVar 33);
     KWord (SA (EVar 32) (-208)) 8 (ELit 1); KWord (SA (EVar 32) (-224)) 8 (ELit 1);
     KRange (EVar 33) 1 (2 ^ 26); KRange (EVar 34) 1 (2 ^ 64 - 1); KRange (EVar 35) 1 (2 ^ 64 - 1)]%Z).
  { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
  ex_run 300%nat [0x85d5c]%Z (SCR [] [] []) HR HK R' HR' Hms.
  all: try g8b_sc2.
  exists R'. split.
  - ex_mem regs Hms.
  - repeat split; try (g8b_reg regs HR'). ex_agree HR HR'.
Qed.

Lemma rg8_I : forall (last : bool) regs m (psrow pdrow off n4 sls : Z) (bs0 bs1 bd : list byte),
  (0 <= off)%Z -> (off + 4 <= n4)%Z -> (if last then off + 4 = n4 else off + 4 < n4)%Z -> (n4 < 2 ^ 28)%Z ->
  (1 <= psrow)%Z -> (psrow + n4 + 4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + n4 < 2 ^ 64)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psrow + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (psrow + off + 4)) 4 = Some bs1 -> length bs1 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (pdrow + off)) 4 = Some bd -> length bd = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 (pdrow + off)) 4 = true ->
  getr regs 22 = Z_to_bv 64 psrow -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 24 = Z_to_bv 64 pdrow -> getr regs 18 = Z_to_bv 64 pdrow ->
  getr regs 19 = Z_to_bv 64 off -> getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 16 = Z_to_bv 64 1 -> getr regs 28 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 32 -> getr regs 26 = Z_to_bv 64 18446744073709551611 -> getr regs 1 = Z_to_bv 64 31 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG8_I m rom)
                (mkst regs' (if last then RG8_T2 else RG8_I) (wbytes m (Z_to_bv 64 (pdrow + off)) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 19 = Z_to_bv 64 (off + 4)
    /\ regs_agree (fun r => In r [12; 15; 17; 19; 27]%list) regs regs'.
Proof.
  intros last regs m psrow pdrow off n4 sls bs0 bs1 bd Hoff Hn4 Hlast Hn4b Hps1 Hps2 Hpd1 Hpd2 Hsls R0 L0 R1 L1 Rd Ld SOK
    H22 H6 H24 H18 H19 H20 H16 H28 H9 H21 H25 H26 H1 H30 H8.
  replace RG8_I with (Z_to_bv 64 0x85d5c) by (apply bv_eq; reflexivity).
  replace RG8_T2 with (Z_to_bv 64 0x85df4) by (apply bv_eq; reflexivity).
  ex_entry regs [psrow; pdrow; off; n4; sls; 32 - sls; extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z HR.
  assert (HK : know_ok SEGS (ex_env regs [psrow; pdrow; off; n4; sls; 32 - sls; extz true 4 (bytes_le_to_Z bs0); extz true 4 (bytes_le_to_Z bs1); extz true 4 (bytes_le_to_Z bd)]%Z) m
    [KRange (EVar 32) 1 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 28); KRange (EVar 35) 4 (2 ^ 28);
     KRange (EVar 36) 1 31; KRange (EVar 37) 1 31]%Z).
  { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
  destruct last; cbv iota in Hlast |- *.
  - ex_run 400%nat [0x85d5c; 0x85df4]%Z (SCR [true; true; true; true; true; false] [EVar 38; EVar 39; EVar 40] []) HR HK R' HR' Hms.
    all: try g8b_sc2.
    exists R'. eexists. split.
    + eapply ex_msteps_mem; [exact Hms |]. cbn [mem_denot s_log e_addr e_width e_val].
      apply ex_wbytes_eq; [reflexivity | g8b_addr regs | reflexivity].
    + repeat split; try (g8b_reg regs HR'). ex_agree HR HR'.
  - ex_run 400%nat [0x85d5c; 0x85df4]%Z (SCR [true; true; true; true; true; true] [EVar 38; EVar 39; EVar 40] []) HR HK R' HR' Hms.
    all: try g8b_sc2.
    exists R'. eexists. split.
    + eapply ex_msteps_mem; [exact Hms |]. cbn [mem_denot s_log e_addr e_width e_val].
      apply ex_wbytes_eq; [reflexivity | g8b_addr regs | reflexivity].
    + repeat split; try (g8b_reg regs HR'). ex_agree HR HR'.
Qed.

Lemma rg8_T2 : forall (last : bool) regs m (s i dh d4 s4 psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 <= dh)%Z -> (dh < 2 ^ 31)%Z -> (if last then i + 1 = dh else i + 1 < dh)%Z ->
  (0 <= d4)%Z -> (0 <= s4)%Z -> (1 <= psrow)%Z -> (psrow + s4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + d4 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 11 = Z_to_bv 64 i -> getr regs 5 = Z_to_bv 64 d4 -> getr regs 7 = Z_to_bv 64 s4 ->
  getr regs 6 = Z_to_bv 64 psrow -> getr regs 22 = Z_to_bv 64 psrow -> getr regs 18 = Z_to_bv 64 pdrow -> getr regs 24 = Z_to_bv 64 pdrow ->
  getr regs 23 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs RG8_T2 m rom) (mkst regs' (if last then RG8_X2 else RG8_H2) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 6 = Z_to_bv 64 (psrow + s4) /\ getr regs' 22 = Z_to_bv 64 (psrow + s4)
    /\ getr regs' 18 = Z_to_bv 64 (pdrow + d4) /\ getr regs' 24 = Z_to_bv 64 (pdrow + d4)
    /\ regs_agree (fun r => In r [6; 11; 12; 15; 16; 18; 22; 24]%list) regs regs'.
Proof.
  intros last regs m s i dh d4 s4 psrow pdrow Hs Hs64 Hi Hidh Hdh Hlast Hd4 Hs4 Hps1 Hps2 Hpd1 Hpd2 Cz Cdh
    H2 H11 H5 H7 H6 H22 H18 H24 H23.
  replace RG8_T2 with (Z_to_bv 64 0x85df4) by (apply bv_eq; reflexivity).
  ex_entry regs [s; i; dh; d4; s4; psrow; pdrow]%Z HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; dh; d4; s4; psrow; pdrow]%Z) m
    [KRange (EVar 32) 240 (2 ^ 64 - 1); KWord (SA (EVar 32) (-120)) 8 (ELit 0); KWord (SA (EVar 32) (-112)) 8 (EVar 34);
     KRange (EVar 33) 0 (2 ^ 31); KRange (EVar 34) 1 (2 ^ 31); KRange (EVar 35) 0 (2 ^ 64 - 1); KRange (EVar 36) 0 (2 ^ 64 - 1);
     KRange (EVar 37) 1 (2 ^ 64 - 1); KRange (EVar 38) 1 (2 ^ 64 - 1)]%Z).
  { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
  destruct last; cbv iota in Hlast |- *.
  - replace RG8_X2 with (Z_to_bv 64 0x85e64) by (apply bv_eq; reflexivity).
    ex_run 400%nat [0x85d38; 0x85e64]%Z (SCR [true; true; true; true; false] [] []) HR HK R' HR' Hms.
    all: try g8b_sc2.
    exists R'. split; [ex_mem regs Hms |]. repeat split; try (g8b_reg regs HR'). ex_agree HR HR'.
  - replace RG8_H2 with (Z_to_bv 64 0x85d38) by (apply bv_eq; reflexivity).
    ex_run 400%nat [0x85d38; 0x85e64]%Z (SCR [true; true; true; true; true] [] []) HR HK R' HR' Hms.
    all: try g8b_sc2.
    exists R'. split; [ex_mem regs Hms |]. repeat split; try (g8b_reg regs HR'). ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma rg8_X1 : forall (nofull : bool) regs m (s psF pdF nfw swpl dwpl : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z -> (0 <= nfw < 2 ^ 26)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0))) ->
  store_ok SEGS m (Z_to_bv 64 (s - 208)) 8 = true -> store_ok SEGS m (Z_to_bv 64 (s - 224)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  (nofull = false ->
     (0 <= psF < 2 ^ 64)%Z /\ (0 <= pdF < 2 ^ 64)%Z /\ (psF mod 4 = 0)%Z /\ (pdF mod 4 = 0)%Z /\
     getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF /\
     rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
     rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw))) ->
  exists regs',
    msteps SEGS (mkst regs RG8_X1 m rom)
                (mkst regs' (if nofull then RG8_X2 else RG8_H2)
                   (if nofull then m else wbytes (wbytes m (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 (s - 224)) (word_to_le_bytes 8 (Z_to_bv 64 1))) rom)
    /\ (nofull = false -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 5 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 7 = Z_to_bv 64 (4 * swpl)
                          /\ getr regs' 20 = Z_to_bv 64 (4 * nfw) /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 32
                          /\ getr regs' 26 = Z_to_bv 64 18446744073709551611 /\ getr regs' 15 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1
                          /\ getr regs' 1 = Z_to_bv 64 31 /\ getr regs' 22 = Z_to_bv 64 psF /\ getr regs' 24 = Z_to_bv 64 pdF)
    /\ regs_agree (fun r => In r [1; 5; 7; 11; 12; 13; 15; 20; 22; 23; 24; 25; 26]%list) regs regs'.
Proof.
  intros nofull regs m s psF pdF nfw swpl dwpl Hs Hs64 Hswpl Hdwpl Hnfw Cnf S208 S224 H2 H14 HF.
  replace RG8_X1 with (Z_to_bv 64 0x85ce8) by (apply bv_eq; reflexivity).
  destruct nofull; cbv iota in Cnf |- *.
  - replace RG8_X2 with (Z_to_bv 64 0x85e64) by (apply bv_eq; reflexivity).
    ex_entry regs [s; dwpl]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; dwpl]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KWord (SA (EVar 32) (-208)) 8 (ELit 1)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 300%nat [0x85d38; 0x85e64]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: try g8b_sc2.
    exists R'. split; [ex_mem regs Hms |]. split; [intros E; discriminate E | ex_agree HR HR'].
  - destruct (HF eq_refl) as (HpsF & HpdF & ALs & ALd & H6 & H18 & Cswpl & Cnfw).
    replace RG8_H2 with (Z_to_bv 64 0x85d38) by (apply bv_eq; reflexivity).
    ex_entry regs [s; psF; pdF; nfw; swpl; dwpl]%Z HR.
    assert (HK : know_ok SEGS (ex_env regs [s; psF; pdF; nfw; swpl; dwpl]%Z) m
      [KRange (EVar 32) 240 (2 ^ 64 - 1); KWord (SA (EVar 32) (-208)) 8 (ELit 0);
       KWord (SA (EVar 32) (-152)) 8 (EVar 36); KWord (SA (EVar 32) (-128)) 8 (EVar 35);
       KAlign (EVar 33) 4; KAlign (EVar 34) 4;
       KRange (EVar 35) 0 (2 ^ 26); KRange (EVar 36) 0 (2 ^ 24); KRange (EVar 37) 0 (2 ^ 24)]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [ex_know1 regs |]). apply Forall_nil. }
    ex_run 300%nat [0x85d38; 0x85e64]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: try g8b_sc2.
    exists R'. split; [ex_mem regs Hms |]. split; [intros _; repeat split; g8b_reg regs HR' | ex_agree HR HR'].
Qed.

Ltac g8g8c_post := repeat split; gres; pin; try reflexivity; solve_regs_agree.

Ltac g8g8c_Ltail n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz :=
  stepb_tk F_85f48 D_85f48 ltac:(condR);
  stepb_tk F_85f50 D_85f50 ltac:(condZ);
  ld4 F_85f58 D_85f58 pd bd Rd Ld;
  sn F_85f5c D_85f5c; sn F_85f60 D_85f60;
  zv F_85f64 D_85f64 (Z_to_bv 64 (pd + d4));
  stw F_85f68 D_85f68 (Z_to_bv 64 pd) SOK;
  stepb_tk F_85f6c D_85f6c ltac:(condZ);
  sltu0 F_85f74 D_85f74; sn F_85f78 D_85f78; sn F_85f7c D_85f7c;
  stepb_tk F_85f80 D_85f80 ltac:(condR);
  zv F_85f88 D_85f88 (Z_to_bv 64 (psl + off + s4));
  stepb_tk F_85f8c D_85f8c ltac:(condZ);
  sltu0 F_85f94 D_85f94;
  ld8w F_85f98 D_85f98 (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_85f9c D_85f9c; sn F_85fa0 D_85fa0;
  stepb_tk F_85fa4 D_85fa4 ltac:(condR);
  sn F_85fac D_85fac; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_85fb0 D_85fb0 (Z_to_bv 64 (off + s4));
  zv F_85fb4 D_85fb4 (Z_to_bv 64 (pd + d4));
  sn F_85fb8 D_85fb8;
  first [ stepb_ft F_85fbc D_85fbc ltac:(condSe); stepj F_85fc0 D_85fc0 | stepb_tk F_85fbc D_85fbc ltac:(condSe) ]; apply mst_refl.

(* [comment removed for export] *)
Lemma rg8_X2 : forall (nolast f3 : bool) regs m (s psl pdl swpl dwpl dh : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nolast then 1 else 0))) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  (nolast = false ->
     (0 <= psl < 2 ^ 64)%Z /\ (0 <= pdl < 2 ^ 64)%Z /\ (psl mod 4 = 0)%Z /\ (pdl mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
     getr regs 10 = Z_to_bv 64 pdl /\
     rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)) /\
     rdn SEGS m (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0))) /\
     rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
     (exists mk : word, rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk)) /\
     rg_rows m s dh) ->
  exists regs',
    msteps SEGS (mkst regs RG8_X2 m rom) (mkst regs' (if nolast then RG_E else RG8_L) m rom)
    /\ (nolast = false -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 6 = Z_to_bv 64 (4 * swpl)
                          /\ getr regs' 17 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 (- dh) /\ getr regs' 16 = Z_to_bv 64 32
                          /\ getr regs' 5 = Z_to_bv 64 (if f3 then 1 else 0) /\ getr regs' 14 = Z_to_bv 64 0
                          /\ getr regs' 7 = Z_to_bv 64 18446744073709551611 /\ getr regs' 28 = Z_to_bv 64 (psl + 4 * swpl)
                          /\ getr regs' 19 = Z_to_bv 64 31 /\ getr regs' 20 = Z_to_bv 64 pdl)
    /\ regs_agree (fun r => In r [5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 28]%list) regs regs'.
Proof.
  intros nolast f3 regs m s psl pdl swpl dwpl dh Hs Hs64 Hswpl Hdwpl Cnl H2 H14 HF.
  unfold RG8_X2, RG_E, RG8_L.
  destruct nolast.
  - eexists. split.
    { ld8 F_85e64 D_85e64 (s - 216)%Z (Z_to_bv 64 1) Cnl.
      stepb_ft F_85e68 D_85e68 ltac:(condR).
      stepj F_85e6c D_85e6c.
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (Hpsl & Hpdl & ALs & ALd & Hdh & H10 & Cpsl & Cf3 & Cswpl & (mk & Cmk) & ROWS).
    destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
    eexists. split.
    + ld8 F_85e64 D_85e64 (s - 216)%Z (Z_to_bv 64 0) Cnl.
      stepb_tk F_85e68 D_85e68 ltac:(condR).
      ld8 F_85e70 D_85e70 (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zand0 F_85e74 D_85e74 andi_3 ALs.
      stepb_tk F_85e78 D_85e78 ltac:(condR).
      sn F_85e80 D_85e80.
      ld8 F_85e84 D_85e84 (s - 144)%Z mk Cmk.
      sn F_85e88 D_85e88.
      slli2 F_85e8c D_85e8c (4 * dwpl)%Z.
      ld8 F_85e90 D_85e90 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
      slli2 F_85e94 D_85e94 (4 * swpl)%Z.
      zand0 F_85e98 D_85e98 andi_3 ALd.
      ld8 F_85e9c D_85e9c (s - 160)%Z (Z_to_bv 64 c50) R50.
      ld8 F_85ea0 D_85ea0 (s - 200)%Z (Z_to_bv 64 c28) R28.
      subw_v F_85ea4 D_85ea4 (c28 - c50)%Z.
      ld8 F_85ea8 D_85ea8 (s - 184)%Z (Z_to_bv 64 c38) R38.
      ld8 F_85eac D_85eac (s - 192)%Z (Z_to_bv 64 c30) R30.
      zv F_85eb0 D_85eb0 (Z_to_bv 64 (c30 + c38)).
      ld8 F_85eb4 D_85eb4 (s - 168)%Z (Z_to_bv 64 c48) R48.
      sn F_85eb8 D_85eb8.
      sn F_85ebc D_85ebc. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(apply and_srai63_min; lia).
      sn F_85ec0 D_85ec0.
      ld8 F_85ec4 D_85ec4 (s - 232)%Z (Z_to_bv 64 (if f3 then 1 else 0)) Cf3.
      sn F_85ec8 D_85ec8. fixv' (Z_to_bv 64 (if f3 then 1 else 0)) ltac:(apply andi1_if).
      slti0 F_85ecc D_85ecc.
      zv F_85ed0 D_85ed0 (Z_to_bv 64 (c30 + c38 + Z.min 0 c48)).
      sn F_85ed4 D_85ed4.
      subw_v F_85ed8 D_85ed8 (c30 + c38 + Z.min 0 c48 - c50)%Z.
      ld8 F_85edc D_85edc (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zv F_85ee0 D_85ee0 (Z_to_bv 64 (psl + 4 * swpl)).
      ld8 F_85ee4 D_85ee4 (s - 176)%Z (Z_to_bv 64 c40) R40.
      subw_v F_85ee8 D_85ee8 (c30 + c38 + Z.min 0 c48 - c50 - c40)%Z.
      sn F_85eec D_85eec.
      sn F_85ef0 D_85ef0. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 + Z.min 0 c48 - c50 - c40))) ltac:(apply and_srai63_min; lia).
      subw_v F_85ef4 D_85ef4 (- dh)%Z.
      sn F_85ef8 D_85ef8.
      sn F_85efc D_85efc.
      apply mst_refl.
    + split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

Lemma rg8_L : forall (f3 last : bool) regs m (s psl off pd s4 d4 n sls : Z) (mk : word) (bs0 bs1 bd : list byte),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= psl)%Z -> (0 <= off)%Z -> (0 <= s4)%Z -> (0 <= d4)%Z ->
  (1 <= psl + off)%Z -> (psl + off + s4 < 2 ^ 64)%Z -> (1 <= pd)%Z -> (pd + d4 < 2 ^ 64)%Z -> (pd + 4 < 2 ^ 64)%Z ->
  (pd + 4 <= s - 240 \/ s <= pd)%Z ->
  (1 <= n < 2 ^ 31)%Z -> (if last then n = 1 else 1 < n)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psl + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  (f3 = false -> psl + off + 8 < 2 ^ 64 /\ rdn SEGS m (Z_to_bv 64 (psl + off + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> length bd = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 11 = Z_to_bv 64 off -> getr regs 10 = Z_to_bv 64 pd -> getr regs 20 = Z_to_bv 64 pd ->
  getr regs 9 = Z_to_bv 64 (- n) -> getr regs 5 = Z_to_bv 64 (if f3 then 1 else 0) ->
  getr regs 17 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 18446744073709551611 ->
  getr regs 19 = Z_to_bv 64 31 -> getr regs 16 = Z_to_bv 64 32 ->
  getr regs 28 = Z_to_bv 64 (psl + s4) -> getr regs 15 = Z_to_bv 64 d4 -> getr regs 6 = Z_to_bv 64 s4 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG8_L m rom)
                (mkst regs' (if last then RG_E else RG8_L) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (off + s4) /\ getr regs' 10 = Z_to_bv 64 (pd + d4) /\ getr regs' 20 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 9 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [9; 10; 11; 18; 20; 21; 22; 23]%list) regs regs'.
Proof.
  intros f3 last regs m s psl off pd s4 d4 n sls mk bs0 bs1 bd Hs Hs64 Hpsl Hoff Hs4 Hd4 Hps1 Hps2 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cpsl Cmk Cz H2 H11 H10 H20 H9 H5 H17 H14 H7 H19 H16 H28 H15 H6 H30 H8.
  unfold RG8_L, RG_E.
  destruct f3.
  - destruct last; eexists; eexists; (split; [
      ld8 F_85f00 D_85f00 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_85f04 D_85f04 (Z_to_bv 64 (psl + off));
      stepb_tk F_85f08 D_85f08 ltac:(condZ);
      stepb_tk F_85f10 D_85f10 ltac:(condZ);
      ld4 F_85f18 D_85f18 (psl + off)%Z bs0 R0 L0;
      sn F_85f1c D_85f1c;
      stepb_tk F_85f20 D_85f20 ltac:(condR);
      g8g8c_Ltail n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz
    | g8g8c_post ]).
  - destruct (R1 eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      ld8 F_85f00 D_85f00 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_85f04 D_85f04 (Z_to_bv 64 (psl + off));
      stepb_tk F_85f08 D_85f08 ltac:(condZ);
      stepb_tk F_85f10 D_85f10 ltac:(condZ);
      ld4 F_85f18 D_85f18 (psl + off)%Z bs0 R0 L0;
      sn F_85f1c D_85f1c;
      stepb_ft F_85f20 D_85f20 ltac:(condR);
      stepb_tk F_85f24 D_85f24 ltac:(condZ);
      stepb_tk F_85f2c D_85f2c ltac:(condZ);
      ld4 F_85f34 D_85f34 (psl + off + 4)%Z bs1 R1' L1;
      sn F_85f38 D_85f38; sn F_85f3c D_85f3c; sn F_85f40 D_85f40; sn F_85f44 D_85f44;
      g8g8c_Ltail n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz
    | g8g8c_post ]).
Qed.

Lemma jt8_gen_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 RG8_JT) 4 = Some (Z_to_le_bytes 4 RG8_JTV).
Proof. unfold RG8_JT, RG_JT, RG8_JTV. vm_refl_bv. Qed.

End Segs8G.
