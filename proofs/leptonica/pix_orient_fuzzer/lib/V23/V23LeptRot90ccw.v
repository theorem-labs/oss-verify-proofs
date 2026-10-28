(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib LeptExec LeptExecX LeptExecW LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23ExecUb.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Ltac exB_sc_hook ::= v23_sc_hook.

Lemma r90_q32s : forall hd : Z, (0 <= hd < 2 ^ 31)%Z ->
  v_sraw (v_add (v_srl (Z_to_bv 64 (2 * hd)) (Z_to_bv 64 59)) (Z_to_bv 64 hd)) (Z_to_bv 64 5) = Z_to_bv 64 (hd / 32).
Proof.
  intros hd Hh. unfold v_srl. rewrite !u_Z2bv by lia.
  change (59 mod 64)%Z with 59%Z. rewrite Z.shiftr_div_pow2 by lia.
  replace ((2 * hd) / 2 ^ 59)%Z with 0%Z by (symmetry; apply Z.div_small; lia).
  rewrite zbv_add. replace (0 + hd)%Z with hd by lia.
  unfold v_sraw. rewrite !u_Z2bv by lia. change (5 mod 32)%Z with 5%Z.
  rewrite (W2Lib.swrap32_small hd) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5)%Z with 32%Z.
  rewrite W2Lib.swrap32_small; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma r90_q32 : forall hd : Z, (0 <= hd < 2 ^ 31)%Z ->
  v_sraw (v_add (v_srl (Sem.mul_div M_MUL (Z_to_bv 64 2) (ext_val true 0 4 (Z_to_bv 64 hd))) (Z_to_bv 64 59))
                (ext_val true 0 4 (Z_to_bv 64 hd))) (Z_to_bv 64 5) = Z_to_bv 64 (hd / 32).
Proof.
  intros hd Hh.
  rewrite !ext_val_sx_id by (first [lia | rewrite u_Z2bv by lia; ex_pow2; lia]).
  rewrite m_mul, zbv_mul. apply r90_q32s. exact Hh.
Qed.

Lemma r90_m32 : forall hd : Z, (0 <= hd < 2 ^ 31)%Z ->
  Sem.mul_div M_MUL (Z_to_bv 64 32)
    (v_sraw (v_add (v_srl (Sem.mul_div M_MUL (Z_to_bv 64 2) (ext_val true 0 4 (Z_to_bv 64 hd))) (Z_to_bv 64 59))
                   (ext_val true 0 4 (Z_to_bv 64 hd))) (Z_to_bv 64 5)) = Z_to_bv 64 (32 * (hd / 32)).
Proof. intros hd Hh. rewrite r90_q32 by lia. rewrite m_mul, zbv_mul. reflexivity. Qed.

Lemma r90_m128 : forall w : Z, (0 <= w < 2 ^ 24)%Z ->
  v_mul (Z_to_bv 64 (-4)) (v_sllw (Z_to_bv 64 w) (Z_to_bv 64 5)) = Z_to_bv 64 (- (128 * w)).
Proof. intros w Hw. rewrite ex_sllw_small by lia. rewrite zbv_mul. f_equal. change (2 ^ 5)%Z with 32%Z. lia. Qed.

Lemma r90_srlw27 : forall w : Z, (0 <= w < 2 ^ 26)%Z -> v_srlw (Z_to_bv 64 (w + 67108864)) (Z_to_bv 64 27) = Z_to_bv 64 0.
Proof.
  intros w Hw. unfold v_srlw. rewrite !u_Z2bv by lia. change (27 mod 32)%Z with 27%Z.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Ltac r90_close :=
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | |- Z_to_bv 64 1 = v_sltu (Z_to_bv 64 0) _ => symmetry; apply zbv_snez; lia
  | |- v_sltu (Z_to_bv 64 0) _ = Z_to_bv 64 1 => apply zbv_snez; lia
  | |- Z_to_bv 64 _ = Sem.mul_div M_MUL (Z_to_bv 64 32) _ => symmetry; apply r90_m32; lia
  | |- Sem.mul_div M_MUL (Z_to_bv 64 32) _ = _ => apply r90_m32; lia
  | |- v_sraw (v_add (v_srl (Sem.mul_div _ _ _) _) _) _ = _ => apply r90_q32; lia
  | |- v_sraw (v_add (v_srl (Z_to_bv 64 _) _) _) _ = _ => apply r90_q32s; lia
  | |- v_mul (Z_to_bv 64 (-4)) _ = _ => apply r90_m128; lia
  | |- v_srlw _ _ = _ => apply r90_srlw27; lia
  | |- Z_to_bv 64 ?a = ext_val true 0 4 (Z_to_bv 64 ?a) => symmetry; apply ext_val_sx_id; [lia | rewrite u_Z2bv by lia; ex_pow2; lia]
  | |- Z_to_bv 64 (Zpos _) = Z_to_bv 64 _ => apply bv_eq; vm_compute; reflexivity
  end.

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.

Definition SLW (m : word -> option byte) (s hd : Z) : word -> option byte :=
  wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
    (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 (32 * (hd / 32)))))
    (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 hd)).

(* [comment removed for export] *)
Lemma cc_S : forall regs m (s wd hd wpld datad datas : Z),
  (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= wd < 2 ^ 31)%Z -> (1 <= hd < 2 ^ 31)%Z -> (1 <= wpld < 2 ^ 24)%Z ->
  (1 <= datad < 2 ^ 64)%Z -> (1 <= datas < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)) ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datad)) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 24 = true ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 8 = Z_to_bv 64 datas ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x9764c) m rom) (mkst regs' (Z_to_bv 64 0x976d4) (SLW m s hd) rom)
    /\ getr regs' 9 = Z_to_bv 64 wd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 hd
    /\ getr regs' 13 = Z_to_bv 64 0x4000000 /\ getr regs' 5 = Z_to_bv 64 0x4000001
    /\ getr regs' 6 = Z_to_bv 64 (- (4 * wpld)) /\ getr regs' 7 = Z_to_bv 64 (- (4 * wpld)) /\ getr regs' 14 = Z_to_bv 64 (4 * wpld)
    /\ getr regs' 28 = Z_to_bv 64 (- (128 * wpld)) /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 17 = Z_to_bv 64 32
    /\ getr regs' 29 = Z_to_bv 64 0 /\ getr regs' 30 = Z_to_bv 64 (hd / 32) /\ getr regs' 19 = Z_to_bv 64 (- 2 ^ 31)
    /\ regs_agree (fun r => In r [5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 19; 25; 28; 29; 30]%list) regs regs'.
Proof.
  intros regs m s wd hd wpld datad datas Hs Hs64 Hwd Hhd Hwp Hdd Hds RW RH RD SOK H2 H10 H8.
  ex_entry regs [s; wd; hd; wpld; datad; datas] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; wd; hd; wpld; datad; datas]) m
    [KWr (SA (EVar 32) (-160)) 24; KWord (SA (EVar 32) (-108)) 4 (EVar 33); KWord (SA (EVar 32) (-112)) 4 (EVar 34);
     KWord (SA (EVar 32) (-136)) 8 (EVar 36);
     KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1);
     KRange (EVar 35) 1 (2 ^ 24 - 1); KRange (EVar 36) 1 (2 ^ 64 - 1); KRange (EVar 37) 1 (2 ^ 64 - 1)]%Z).
  { ex_know regs. }
  ex_run 400%nat [0x976d4]%Z (SCR [] [] []) HR HK R' HR' Hms.
  all: cycle 1.
  { exists R'. split.
    - unfold SLW. eapply ex_msteps_mem; [exact Hms|].
      cbn [mem_denot s_log e_addr e_width e_val].
      repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | ex_bytes_eq regs ]).
      all: r90_close.
    - repeat split; try (exB_reg regs HR'); try r90_close.
      ex_agree HR HR'. }
Qed.

End Segs.

#[local] Ltac exB_sc_hook ::= v23_sc_hook.

Lemma kzb_un : forall z : Z, (- 2 ^ 64 <= z < 0)%Z -> bv_unsigned (Z_to_bv 64 z) = (z + 2 ^ 64)%Z.
Proof. intros z Hz. rewrite u_Z2bv_mod. symmetry. apply (Z.mod_unique z (2 ^ 64) (-1) (z + 2 ^ 64)); lia. Qed.

Ltac kzb_stop :=
  lazymatch goal with
  | |- exists _, msteps _ _ (mkst _ (Z_to_bv 64 ?p) _ _) /\ _ => constr:(p)
  end.
Ltac kzb_run dirs reads HR HK R' HR' Hms := let p := kzb_stop in ex_run 400%nat [p]%Z (SCR dirs reads []) HR HK R' HR' Hms.
Ltac kzb_norm := repeat first [ rewrite m_mul | rewrite zbv_mul | rewrite ex_ptr_val | rewrite zbv_addi ].
Ltac kzb_u :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => first [ rewrite (u_Z2bv z) by lia | rewrite (kzb_un z) by lia ]
  end.
Ltac kzb_dec :=
  repeat match goal with
  | |- context [(?x <? ?y)%Z] => first [ rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia ]
  | |- context [(?x =? ?y)%Z] => first [ rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia ]
  end.
Ltac kzb_br :=
  lazymatch goal with |- branch_taken _ _ _ = _ => idtac end;
  kzb_norm; rewrite ?alu_sltu, ?alu_xor; unfold v_sltu, c_ltu;
  cbn [branch_taken]; unfold bv_eqb, bv_ltu; kzb_u; kzb_dec;
  first [ reflexivity | (lazymatch goal with |- ?G => is_closed_term G end; vm_compute; reflexivity) ].
Ltac kzb_flat := lazymatch goal with |- (0 <= _)%Z /\ _ => idtac end; kzb_norm; kzb_u; lia.

Section SegsB.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma cc_Kz : forall regs m (lines lined wpld k datas : Z) (bs : list byte) (v : word),
  rdn SEGS m (Z_to_bv 64 (lines + 4 * k)) 4 = Some bs -> bytes_le_to_Z bs = bv_unsigned v -> v_lw v = Z_to_bv 64 0 ->
  (0 <= k < 2 ^ 24)%Z -> (1 <= lines)%Z -> (lines + 4 * k + 4 <= 2 ^ 64)%Z -> (lines mod 4 = 0)%Z -> (1 <= datas < 2 ^ 64)%Z ->
  (1 <= wpld < 2 ^ 24)%Z -> (128 * wpld < lined < 2 ^ 64)%Z ->
  getr regs 23 = Z_to_bv 64 k -> getr regs 21 = Z_to_bv 64 lines -> getr regs 20 = Z_to_bv 64 lined ->
  getr regs 28 = Z_to_bv 64 (- (128 * wpld)) -> getr regs 8 = Z_to_bv 64 datas -> getr regs 16 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x977a0) m rom) (mkst regs' (Z_to_bv 64 0x97798) m rom)
    /\ getr regs' 20 = Z_to_bv 64 (lined - 128 * wpld)
    /\ regs_agree (fun r => In r [9; 15; 20; 24]%list) regs regs'.
Proof.
  intros regs m lines lined wpld k datas bs v RB HB HV Hk Hl Hlk Hla Hd Hw Hld H23 H21 H20 H28 H8 H16 H29 H22.
  ex_entry regs [k; lines; lined; (- (128 * wpld))%Z; datas; wpld] HR.
  assert (HK : know_ok SEGS (ex_env regs [k; lines; lined; (- (128 * wpld))%Z; datas; wpld]) m
    [KRange (EVar 32) 0 (2 ^ 24 - 1); KRange (EVar 33) 1 (2 ^ 64 - 4); KAlign (EVar 33) 4; KRange (EVar 34) 129 (2 ^ 64 - 1);
     KRange (EVar 36) 1 (2 ^ 64 - 1); KRange (EVar 37) 1 (2 ^ 24 - 1)]%Z) by (ex_know regs).
  kzb_run [true; true; true; true] [ELit 0] HR HK R' HR' Hms.
  all: try solve [exists R'; split; [ex_mem regs Hms|]; split; [v23_reg regs HR'|ex_agree HR HR']].
  all: try solve [kzb_br].
  all: try solve [kzb_flat].
  all: exists bs; split; [kzb_norm; rewrite <- RB; f_equal; f_equal; lia
                         | rewrite HB; transitivity (v_lw v); [unfold v_lw, extz; reflexivity | exact HV]].
Qed.

Lemma cc_Knz : forall regs m (lines lined k datas : Z) (bs : list byte) (v : word),
  rdn SEGS m (Z_to_bv 64 (lines + 4 * k)) 4 = Some bs -> bytes_le_to_Z bs = bv_unsigned v -> v_lw v <> Z_to_bv 64 0 ->
  (0 <= k < 2 ^ 24)%Z -> (1 <= lines)%Z -> (lines + 4 * k + 4 <= 2 ^ 64)%Z -> (lines mod 4 = 0)%Z -> (1 <= datas < 2 ^ 64)%Z ->
  getr regs 23 = Z_to_bv 64 k -> getr regs 21 = Z_to_bv 64 lines -> getr regs 20 = Z_to_bv 64 lined ->
  getr regs 8 = Z_to_bv 64 datas -> getr regs 16 = Z_to_bv 64 1 ->
  getr regs 5 = Z_to_bv 64 0x4000001 -> getr regs 13 = Z_to_bv 64 0x4000000 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x977a0) m rom) (mkst regs' (Z_to_bv 64 0x977f8) m rom)
    /\ getr regs' 24 = v_lw v /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 lined
    /\ regs_agree (fun r => In r [9; 15; 24; 25]%list) regs regs'.
Proof.
  intros regs m lines lined k datas bs v RB HB HV Hk Hl Hlk Hla Hd H23 H21 H20 H8 H16 H5 H13.
  unfold v_lw in HV |- *.
  remember (bv_swrap 32 (bv_unsigned v)) as zv eqn:Hzv.
  ex_entry regs [k; lines; lined; datas; zv] HR.
  assert (HK : know_ok SEGS (ex_env regs [k; lines; lined; datas; zv]) m
    [KRange (EVar 32) 0 (2 ^ 24 - 1); KRange (EVar 33) 1 (2 ^ 64 - 4); KAlign (EVar 33) 4; KRange (EVar 35) 1 (2 ^ 64 - 1)]%Z)
    by (ex_know regs).
  kzb_run [true; true; false] [EVar 36] HR HK R' HR' Hms.
  all: try solve [exists R'; split; [ex_mem regs Hms|]; repeat split; try (v23_reg regs HR'); ex_agree HR HR'].
  all: try solve [kzb_br].
  all: try solve [kzb_flat].
  all: try solve [lazymatch goal with |- branch_taken _ _ _ = _ => idtac end; subst zv; cbn [branch_taken]; unfold bv_eqb;
                  apply Z.eqb_neq; intro Hne; apply HV; apply bv_eq; exact Hne].
  all: exists bs; split; [kzb_norm; rewrite <- RB; f_equal; f_equal; lia | rewrite HB, Hzv; unfold extz; reflexivity].
Qed.

End SegsB.

#[local] Ltac exB_sc_hook ::= v23_sc_hook.

#[local] Ltac cm_tgt := lazymatch goal with |- context [msteps _ _ (mkst _ (Z_to_bv 64 ?q) _ _)] => constr:(q) end.
#[local] Ltac cm_run fuel scr HR HK R' HR' Hms := let q := cm_tgt in ex_run fuel [q]%Z scr HR HK R' HR' Hms.

Lemma cm_sltu_neg : forall a k : Z, (0 <= a)%Z -> (1 <= k)%Z -> (a + k < 2 ^ 64)%Z ->
  alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 (- k)) = Z_to_bv 64 1.
Proof.
  intros a k Ha Hk Hak.
  rewrite (Z_to_bv64_eqm (- k) (2 ^ 64 - k)) by (rewrite <- (Z_mod_plus_full (- k) 1 (2 ^ 64)); f_equal; lia).
  rewrite alu_sltu, WalksLib.v_sltu_Z by lia.
  rewrite (proj2 (Z.ltb_lt a (2 ^ 64 - k))) by lia. reflexivity.
Qed.

Lemma cm_sltu_ge : forall a b : Z, (0 <= b <= a)%Z -> (a < 2 ^ 64)%Z ->
  alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof. intros a b Hb Ha. rewrite alu_sltu. apply zbv_sltu_ge; lia. Qed.

Lemma cm_slt0 : forall a : Z, (0 <= a < 2 ^ 63)%Z -> alu64 ALU_SLT (Z_to_bv 64 a) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. intros a Ha. rewrite alu_slt, WalksLib.v_slt_Z by lia. rewrite (proj2 (Z.ltb_ge a 0)) by lia. reflexivity. Qed.

Lemma cm_sraw5 : forall x : Z, (0 <= x < 2 ^ 31)%Z -> v_sraw (Z_to_bv 64 x) (Z_to_bv 64 5) = Z_to_bv 64 (x / 32).
Proof.
  intros x Hx. unfold v_sraw. rewrite !u_Z2bv by lia. change (5 mod 32)%Z with 5%Z.
  rewrite (W2Lib.swrap32_small x) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5)%Z with 32%Z.
  rewrite W2Lib.swrap32_small; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

#[local] Ltac cm_norm := repeat first [ rewrite ex_sx32 by lia | rewrite w_subw | rewrite w_addw | rewrite w_mulw | rewrite w_sraw
  | rewrite m_mul | rewrite zbv_mul | rewrite ex_ptr_val | rewrite LeptRop.subw_fit by lia | rewrite LeptRop.addw_fit by lia
  | rewrite W2Lib.zbv_mulw_small by lia | rewrite cm_sraw5 by lia ].
#[local] Ltac cm_bits :=
  repeat match goal with
  | |- context [alu64 ALU_SLTU (Z_to_bv 64 ?a) (Z_to_bv 64 (- ?k))] => rewrite (cm_sltu_neg a k) by lia
  | |- context [alu64 ALU_SLTU (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (cm_sltu_ge a b) by lia
  | |- context [alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 ?p)] => rewrite (sltu0_nz p) by lia
  | |- context [alu64 ALU_SLT (Z_to_bv 64 ?a) (Z_to_bv 64 0)] => rewrite (cm_slt0 a) by lia
  end.
#[local] Ltac exB_sc_hook ::= first [ v23_sc_hook | (v23_norm; ex_br)
  | (cm_norm; cm_bits; lazymatch goal with |- ?G => is_closed_term G end; vm_compute; reflexivity)
  | (cm_norm; first [ ex_br | (apply v23_ne_f; lia) | (apply v23_eq_t; lia) ]) ].

#[local] Ltac cm_anorm := cm_norm; rewrite ?zbv_addi, ?Z.add_0_r.
#[local] Ltac cm_flat := cm_anorm; rewrite ?u_Z2bv by lia; lia.
#[local] Ltac cm_sok :=
  cm_anorm;
  match goal with H : store_ok _ _ (Z_to_bv 64 ?a') ?n = true |- _ _ _ (Z_to_bv 64 ?a) ?n = true =>
    replace a with a' by lia; exact H end.
#[local] Ltac cm_addr regs :=
  ex_unfoldE; unfold adenot; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  cm_anorm; first [ reflexivity | f_equal; lia ].

#[local] Ltac cm_sbit Hb := lazymatch goal with |- branch_taken _ _ _ = _ => idtac end;
  rewrite w_sllw; cbn [branch_taken]; unfold c_lts in Hb; rewrite Hb; reflexivity.

#[local] Ltac cm_rdbz Hzt :=
  match goal with
  | H : rdn _ _ (Z_to_bv 64 ?a') ?n = Some ?bs0, L : bytes_le_to_Z ?bs0 = _ |- exists _, rdn _ _ _ ?n = Some _ /\ _ =>
      exists bs0; split;
      [ cm_anorm; match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with a' by lia; exact H end
      | unfold extz; rewrite Hzt, <- L; reflexivity ]
  end.

Section SegsB2.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma cc_Kn : forall regs m (k nsw : Z), (0 <= k)%Z -> (k + 1 < nsw < 2 ^ 31)%Z ->
  getr regs 23 = Z_to_bv 64 k -> getr regs 30 = Z_to_bv 64 nsw ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x97798) m rom) (mkst regs' (Z_to_bv 64 0x977a0) m rom)
    /\ getr regs' 23 = Z_to_bv 64 (k + 1)
    /\ regs_agree (fun r => In r [23]%list) regs regs'.
Proof.
  intros regs m k nsw Hk Hn H23 H30.
  ex_entry regs [k; nsw] HR.
  assert (HK : know_ok SEGS (ex_env regs [k; nsw]) m [KRange (EVar 32) 0 (2 ^ 31 - 3); KRange (EVar 33) 2 (2 ^ 31 - 1)]%Z) by (ex_know regs).
  cm_run 400%nat (SCR [false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. split; [v23_reg regs HR'|]. ex_agree HR HR'. }
Qed.

Lemma cc_Kx : forall regs m (s k nsw hd : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (k + 1 = nsw)%Z -> (0 <= nsw < 2 ^ 31)%Z ->
  (0 <= hd < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 23 = Z_to_bv 64 k -> getr regs 30 = Z_to_bv 64 nsw ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x97798) m rom) (mkst regs' (Z_to_bv 64 0x978f8) m rom)
    /\ getr regs' 25 = Z_to_bv 64 hd
    /\ regs_agree (fun r => In r [23; 25]%list) regs regs'.
Proof.
  intros regs m s k nsw hd Hs Hs64 Hk Hn Hhd RH H2 H23 H30.
  subst nsw.
  ex_entry regs [s; k; hd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; k; hd]) m
    [KWord (SA (EVar 32) (-112)) 4 (EVar 34); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs).
  cm_run 400%nat (SCR [true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. split; [v23_reg regs HR'|]. ex_agree HR HR'. }
Qed.

(* [comment removed for export] *)
Lemma cc_Mn : forall regs m (mm lined wpld : Z), (0 <= mm)%Z -> (mm + 1 < 32)%Z ->
  (1 <= wpld < 2 ^ 24)%Z -> (4 * wpld < lined < 2 ^ 64)%Z ->
  getr regs 9 = Z_to_bv 64 mm -> getr regs 20 = Z_to_bv 64 lined -> getr regs 25 = Z_to_bv 64 lined -> getr regs 15 = Z_to_bv 64 lined ->
  getr regs 6 = Z_to_bv 64 (- (4 * wpld)) -> getr regs 7 = Z_to_bv 64 (- (4 * wpld)) -> getr regs 14 = Z_to_bv 64 (4 * wpld) ->
  getr regs 17 = Z_to_bv 64 32 -> getr regs 22 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x97888) m rom) (mkst regs' (Z_to_bv 64 0x977f8) m rom)
    /\ getr regs' 9 = Z_to_bv 64 (mm + 1) /\ getr regs' 20 = Z_to_bv 64 (lined - 4 * wpld)
    /\ getr regs' 25 = Z_to_bv 64 (lined - 4 * wpld)
    /\ regs_agree (fun r => In r [9; 12; 15; 20; 25; 31]%list) regs regs'.
Proof.
  intros regs m mm lined wpld Hm Hm1 Hw Hl H9 H20 H25 H15 H6 H7 H14 H17 H22.
  ex_entry regs [mm; lined; (- (4 * wpld))%Z; (4 * wpld)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [mm; lined; (- (4 * wpld))%Z; (4 * wpld)%Z]) m
    [KRange (EVar 32) 0 30; KRange (EVar 33) 5 (2 ^ 64 - 1); KRange (EVar 35) 4 (2 ^ 26)]%Z) by (ex_know regs).
  cm_run 400%nat (SCR [true; true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. repeat split; try (v23_reg regs HR'). ex_agree HR HR'. }
Qed.

Lemma cc_Mx : forall regs m (mm lined wpld : Z), (mm + 1 = 32)%Z ->
  (1 <= wpld < 2 ^ 24)%Z -> (4 * wpld < lined < 2 ^ 64)%Z ->
  getr regs 9 = Z_to_bv 64 mm -> getr regs 20 = Z_to_bv 64 lined -> getr regs 25 = Z_to_bv 64 lined -> getr regs 15 = Z_to_bv 64 lined ->
  getr regs 6 = Z_to_bv 64 (- (4 * wpld)) -> getr regs 7 = Z_to_bv 64 (- (4 * wpld)) -> getr regs 14 = Z_to_bv 64 (4 * wpld) ->
  getr regs 17 = Z_to_bv 64 32 -> getr regs 22 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x97888) m rom) (mkst regs' (Z_to_bv 64 0x97798) m rom)
    /\ getr regs' 20 = Z_to_bv 64 (lined - 4 * wpld)
    /\ regs_agree (fun r => In r [9; 12; 15; 20; 25; 31]%list) regs regs'.
Proof.
  intros regs m mm lined wpld Hm Hw Hl H9 H20 H25 H15 H6 H7 H14 H17 H22.
  assert (mm = 31)%Z by lia. subst mm.
  ex_entry regs [lined; (- (4 * wpld))%Z; (4 * wpld)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; (- (4 * wpld))%Z; (4 * wpld)%Z]) m
    [KRange (EVar 32) 5 (2 ^ 64 - 1); KRange (EVar 34) 4 (2 ^ 26)]%Z) by (ex_know regs).
  cm_run 400%nat (SCR [true; true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. repeat split; try (v23_reg regs HR'). ex_agree HR HR'. }
Qed.

(* [comment removed for export] *)
Lemma cc_M : forall (b : bool) regs m (s lined wd j mm : Z) (v : word) (bt : list byte) (vt : word),
  c_lts (v_sllw (v_lw v) (Z_to_bv 64 mm)) (Z_to_bv 64 0) = b ->
  (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= j < wd)%Z -> (wd < 2 ^ 31)%Z -> (0 <= mm < 32)%Z ->
  (1 <= lined)%Z -> (lined mod 4 = 0)%Z -> (lined + 4 * ((wd - 1 - j) / 32) + 4 <= 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)) ->
  rdn SEGS m (Z_to_bv 64 (lined + 4 * ((wd - 1 - j) / 32))) 4 = Some bt -> bytes_le_to_Z bt = bv_unsigned vt ->
  store_ok SEGS m (Z_to_bv 64 (lined + 4 * ((wd - 1 - j) / 32))) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 24 = v_lw v -> getr regs 9 = Z_to_bv 64 mm ->
  getr regs 20 = Z_to_bv 64 lined -> getr regs 25 = Z_to_bv 64 lined -> getr regs 11 = Z_to_bv 64 j ->
  getr regs 19 = Z_to_bv 64 (- 2 ^ 31) ->
  exists regs' m',
    msteps SEGS (mkst regs (Z_to_bv 64 0x977f8) m rom) (mkst regs' (Z_to_bv 64 0x97888) m' rom)
    /\ (if b then exists wv : word, m' = wbytes m (Z_to_bv 64 (lined + 4 * ((wd - 1 - j) / 32))) (word_to_le_bytes 4 wv) else m' = m)
    /\ getr regs' 15 = Z_to_bv 64 lined
    /\ regs_agree (fun r => In r [1; 12; 15; 26; 27; 31]%list) regs regs'.
Proof.
  intros b regs m s lined wd j mm v bt vt Hb Hs Hs64 Hj Hwd Hmm Hl1 Hl4 Hlb RW RT LT SOK H2 H24 H9 H20 H25 H11 H19.
  assert (Hw32 : (0 <= (wd - 1 - j) / 32)%Z) by (apply Z.div_pos; lia).
  assert (Hw32b : ((wd - 1 - j) / 32 < 2 ^ 31)%Z) by (apply Z.div_lt_upper_bound; lia).
  assert (Hq : ((-1 * j + (wd + -1)) / 32 = (wd - 1 - j) / 32)%Z) by (f_equal; lia).
  unfold v_lw in H24, Hb.
  set (zv := bv_swrap 32 (bv_unsigned v)) in *. clearbody zv.
  remember (bv_swrap 32 (bv_unsigned vt)) as zt eqn:Hzt.
  ex_entry regs [s; lined; wd; j; mm; zv; zt] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; lined; wd; j; mm; zv; zt]) m
    [KWord (SA (EVar 32) (-108)) 4 (EVar 34); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 4); KAlign (EVar 33) 4;
     KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 2); KRange (EVar 36) 0 31]%Z) by (ex_know regs).
  destruct b.
  - cm_run 400%nat (SCR [false; true; true; true; true] [EVar 38] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R'. eexists. split; [exact Hms|]. split.
      - eexists. cbn [mem_denot]. apply ex_wbytes_eq; [reflexivity | cm_addr regs | reflexivity].
      - split; [v23_reg regs HR'|]. ex_agree HR HR'. }
    all: first [ cm_sbit Hb | cm_rdbz Hzt | cm_flat | cm_sok ].
  - cm_run 400%nat (SCR [true] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R', m. split; [ex_mem regs Hms|]. split; [reflexivity|]. split; [v23_reg regs HR'|]. ex_agree HR HR'. }
    all: first [ cm_sbit Hb | cm_rdbz Hzt | cm_flat ].
Qed.

End SegsB2.

#[local] Ltac exB_sc_hook ::= v23_sc_hook.

#[local] Ltac cc_tgt := lazymatch goal with |- context [msteps _ _ (mkst _ (Z_to_bv 64 ?q) _ _)] => constr:(q) end.
#[local] Ltac cc_run fuel scr HR HK R' HR' Hms := let q := cc_tgt in ex_run fuel [q]%Z scr HR HK R' HR' Hms.

Lemma ccT_sltu_neg : forall a k : Z, (0 <= a)%Z -> (1 <= k)%Z -> (a + k < 2 ^ 64)%Z ->
  alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 (- k)) = Z_to_bv 64 1.
Proof.
  intros a k Ha Hk Hak.
  rewrite (Z_to_bv64_eqm (- k) (2 ^ 64 - k)) by (rewrite <- (Z_mod_plus_full (- k) 1 (2 ^ 64)); f_equal; lia).
  rewrite alu_sltu, WalksLib.v_sltu_Z by lia.
  rewrite (proj2 (Z.ltb_lt a (2 ^ 64 - k))) by lia. reflexivity.
Qed.

Lemma ccT_sltu_ge : forall a b : Z, (0 <= b <= a)%Z -> (a < 2 ^ 64)%Z ->
  alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof. intros a b Hb Ha. rewrite alu_sltu. apply zbv_sltu_ge; lia. Qed.

Lemma ccT_slt0 : forall a : Z, (0 <= a < 2 ^ 63)%Z -> alu64 ALU_SLT (Z_to_bv 64 a) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. intros a Ha. rewrite alu_slt, WalksLib.v_slt_Z by lia. rewrite (proj2 (Z.ltb_ge a 0)) by lia. reflexivity. Qed.

Lemma ccT_sraw5 : forall x : Z, (0 <= x < 2 ^ 31)%Z -> v_sraw (Z_to_bv 64 x) (Z_to_bv 64 5) = Z_to_bv 64 (x / 32).
Proof.
  intros x Hx. unfold v_sraw. rewrite !u_Z2bv by lia. change (5 mod 32)%Z with 5%Z.
  rewrite (W2Lib.swrap32_small x) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5)%Z with 32%Z.
  rewrite W2Lib.swrap32_small; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

#[local] Ltac cc_norm := repeat first [ rewrite ex_sx32 by lia | rewrite w_subw | rewrite w_addw | rewrite w_mulw | rewrite w_sraw
  | rewrite m_mul | rewrite zbv_mul | rewrite ex_ptr_val | rewrite LeptRop.subw_fit by lia | rewrite LeptRop.addw_fit by lia
  | rewrite W2Lib.zbv_mulw_small by lia | rewrite ccT_sraw5 by lia ].
#[local] Ltac cc_bits :=
  repeat match goal with
  | |- context [alu64 ALU_SLTU (Z_to_bv 64 ?a) (Z_to_bv 64 (- ?k))] => rewrite (ccT_sltu_neg a k) by lia
  | |- context [alu64 ALU_SLTU (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => rewrite (ccT_sltu_ge a b) by lia
  | |- context [alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 ?p)] => rewrite (sltu0_nz p) by lia
  | |- context [alu64 ALU_SLT (Z_to_bv 64 ?a) (Z_to_bv 64 0)] => rewrite (ccT_slt0 a) by lia
  end.
#[local] Ltac exB_sc_hook ::= first [ v23_sc_hook | (v23_norm; ex_br)
  | (cc_norm; cc_bits; lazymatch goal with |- ?G => is_closed_term G end; vm_compute; reflexivity)
  | (cc_norm; first [ ex_br | (apply v23_ne_f; lia) | (apply v23_eq_t; lia) ]) ].
#[local] Ltac cc_reg regs HR' :=
  lazymatch goal with |- getr _ ?k = _ =>
    rewrite (reg_val _ _ _ k HR');
    match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
    ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
    repeat match goal with H : getr regs _ = _ |- _ => progress rewrite H end;
    cc_norm; first [ reflexivity | (f_equal; lia) ]
  end.

#[local] Ltac cc_bit Hb := rewrite <- Hb; cbn [branch_taken]; unfold c_eq; f_equal;
  rewrite alu_and, alu_xor, w_srlw; unfold v_and, v_andi, v_xor, v_xori, v_lw; reflexivity.
#[local] Ltac cc_anorm := cc_norm; rewrite ?zbv_addi, ?Z.add_0_r.
#[local] Ltac cc_rdb :=
  match goal with
  | H : rdn _ _ (Z_to_bv 64 ?a') ?n = Some ?bs0, L : bytes_le_to_Z ?bs0 = _ |- exists _, rdn _ _ _ ?n = Some _ /\ _ =>
      exists bs0; split;
      [ cc_anorm; match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with a' by lia; exact H end
      | unfold extz; rewrite <- L; reflexivity ]
  end.
#[local] Ltac cc_flat := cc_anorm; rewrite ?u_Z2bv by lia; lia.
#[local] Ltac cc_sok :=
  cc_anorm;
  match goal with H : store_ok _ _ (Z_to_bv 64 ?a') ?n = true |- _ _ _ (Z_to_bv 64 ?a) ?n = true =>
    replace a with a' by lia; exact H end.
#[local] Ltac cc_addr regs :=
  ex_unfoldE; unfold adenot; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  cc_anorm; first [ reflexivity | f_equal; lia ].

Section SegsT.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma cc_Jw : forall regs m (s wd hd datas wpls datad wpld j : Z),
  (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= j < wd)%Z -> (wd < 2 ^ 31)%Z -> (32 <= hd < 2 ^ 31)%Z ->
  (0 <= wpls)%Z -> (1 <= wpld)%Z -> (4 * wpld * hd <= 2 ^ 26)%Z -> (4 * wpls * wd <= 2 ^ 26)%Z ->
  (1 <= datad)%Z -> (datad + 4 * wpld * hd < 2 ^ 64)%Z -> (1 <= datas)%Z -> (datas + 4 * wpls * wd < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datad)) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 11 = Z_to_bv 64 j -> getr regs 9 = Z_to_bv 64 wd ->
  getr regs 25 = Z_to_bv 64 hd -> getr regs 18 = Z_to_bv 64 wpls -> getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 8 = Z_to_bv 64 datas -> getr regs 16 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 32 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x976d4) m rom) (mkst regs' (Z_to_bv 64 0x977a0) m rom)
    /\ getr regs' 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1)) /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j))
    /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [9; 12; 15; 20; 21; 22; 23]%list) regs regs'.
Proof.
  intros regs m s wd hd datas wpls datad wpld j Hs Hs64 Hj Hwd Hhd Hwps Hwpd Hszd Hszs Hdd Hddb Hds Hdsb RD R1 RH H2 H11 H9 H25 H18 H10 H8 H16 H17.
  assert (Hwps2 : (wpls <= 2 ^ 24)%Z) by nia.
  assert (Hwpd2 : (wpld <= 2 ^ 24)%Z) by nia.
  assert (Hpd : (0 <= 4 * wpld * hd)%Z) by nia.
  assert (Hps : (0 <= 4 * wpls * wd)%Z) by nia.
  assert (Hm1 : (0 <= (hd - 1) * wpld <= 2 ^ 24)%Z) by nia.
  assert (Hm2 : (0 <= (wd - 1 - j) * wpls <= 2 ^ 24)%Z) by nia.
  ex_entry regs [s; j; wd; hd; wpls; wpld; datas; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; j; wd; hd; wpls; wpld; datas; datad]) m
    [KWord (SA (EVar 32) (-136)) 8 (EVar 39); KWord (SA (EVar 32) (-152)) 8 (ELit 1); KWord (SA (EVar 32) (-160)) 8 (EVar 35);
     KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 1 (2 ^ 31 - 1);
     KRange (EVar 36) 0 (2 ^ 24); KRange (EVar 37) 1 (2 ^ 24); KRange (EVar 38) 1 (2 ^ 64 - 1); KRange (EVar 39) 1 (2 ^ 64 - 1)]%Z).
  { ex_know regs. }
  cc_run 400%nat (SCR [true; true; true; true; true; true; true; true; false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. repeat split; try (first [v23_reg regs HR' | cc_reg regs HR']); try (rewrite WalksLib.v_slt_Z by lia; rewrite (proj2 (Z.ltb_ge wpld 1)) by lia; reflexivity). ex_agree HR HR'. }
Qed.

(* [comment removed for export] *)
Lemma cc_Jt : forall regs m (s wd hd datas wpls datad wpld j : Z),
  (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= j < wd)%Z -> (wd < 2 ^ 31)%Z -> (1 <= hd < 32)%Z ->
  (0 <= wpls)%Z -> (1 <= wpld)%Z -> (4 * wpld * hd <= 2 ^ 26)%Z -> (4 * wpls * wd <= 2 ^ 26)%Z ->
  (1 <= datad)%Z -> (datad + 4 * wpld * hd < 2 ^ 64)%Z -> (1 <= datas)%Z -> (datas + 4 * wpls * wd < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datad)) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 hd)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 11 = Z_to_bv 64 j -> getr regs 9 = Z_to_bv 64 wd ->
  getr regs 25 = Z_to_bv 64 hd -> getr regs 18 = Z_to_bv 64 wpls -> getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 8 = Z_to_bv 64 datas -> getr regs 16 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 32 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x976d4) m rom) (mkst regs' (Z_to_bv 64 0x978f8) m rom)
    /\ getr regs' 20 = Z_to_bv 64 (datad + 4 * wpld * (hd - 1)) /\ getr regs' 21 = Z_to_bv 64 (datas + 4 * wpls * (wd - 1 - j))
    /\ getr regs' 22 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [9; 12; 15; 20; 21; 22]%list) regs regs'.
Proof.
  intros regs m s wd hd datas wpls datad wpld j Hs Hs64 Hj Hwd Hhd Hwps Hwpd Hszd Hszs Hdd Hddb Hds Hdsb RD R1 RH H2 H11 H9 H25 H18 H10 H8 H16 H17.
  assert (Hwps2 : (wpls <= 2 ^ 24)%Z) by nia.
  assert (Hwpd2 : (wpld <= 2 ^ 24)%Z) by nia.
  assert (Hpd : (0 <= 4 * wpld * hd)%Z) by nia.
  assert (Hps : (0 <= 4 * wpls * wd)%Z) by nia.
  assert (Hm1 : (0 <= (hd - 1) * wpld <= 2 ^ 24)%Z) by nia.
  assert (Hm2 : (0 <= (wd - 1 - j) * wpls <= 2 ^ 24)%Z) by nia.
  ex_entry regs [s; j; wd; hd; wpls; wpld; datas; datad] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; j; wd; hd; wpls; wpld; datas; datad]) m
    [KWord (SA (EVar 32) (-136)) 8 (EVar 39); KWord (SA (EVar 32) (-152)) 8 (ELit 1); KWord (SA (EVar 32) (-160)) 8 (EVar 35);
     KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 1 31;
     KRange (EVar 36) 0 (2 ^ 24); KRange (EVar 37) 1 (2 ^ 24); KRange (EVar 38) 1 (2 ^ 64 - 1); KRange (EVar 39) 1 (2 ^ 64 - 1)]%Z).
  { ex_know regs. }
  cc_run 400%nat (SCR [true; true; true; true; true; true; true; true; true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. repeat split; try (first [v23_reg regs HR' | cc_reg regs HR']); try (rewrite WalksLib.v_slt_Z by lia; rewrite (proj2 (Z.ltb_ge wpld 1)) by lia; reflexivity). ex_agree HR HR'. }
Qed.

(* [comment removed for export] *)
Lemma cc_T0e : forall regs m (s hd a7 : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= hd < 2 ^ 31)%Z -> (0 <= a7 < 2 ^ 31)%Z -> (hd <= a7)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 a7)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 25 = Z_to_bv 64 hd ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x978f8) m rom) (mkst regs' (Z_to_bv 64 0x976c4) m rom)
    /\ regs_agree (fun r => In r [12]%list) regs regs'.
Proof.
  intros regs m s hd a7 Hs Hs64 Hhd Ha7 Hle RA H2 H25.
  ex_entry regs [s; hd; a7] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; hd; a7]) m
    [KWord (SA (EVar 32) (-144)) 8 (EVar 34); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs).
  cc_run 400%nat (SCR [true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. ex_agree HR HR'. }
Qed.

Lemma cc_T0s : forall regs m (s hd a7 lined : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= hd < 2 ^ 31)%Z -> (0 <= a7 < 2 ^ 31)%Z -> (a7 < hd)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 a7)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 25 = Z_to_bv 64 hd -> getr regs 20 = Z_to_bv 64 lined ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x978f8) m rom) (mkst regs' (Z_to_bv 64 0x97908) m rom)
    /\ getr regs' 23 = Z_to_bv 64 lined /\ getr regs' 24 = Z_to_bv 64 a7
    /\ regs_agree (fun r => In r [12; 23; 24]%list) regs regs'.
Proof.
  intros regs m s hd a7 lined Hs Hs64 Hhd Ha7 Hlt RA H2 H25 H20.
  ex_entry regs [s; hd; a7; lined] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; hd; a7; lined]) m
    [KWord (SA (EVar 32) (-144)) 8 (EVar 34); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs).
  cc_run 400%nat (SCR [false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. repeat split; try (v23_reg regs HR'). ex_agree HR HR'. }
Qed.

(* [comment removed for export] *)
Lemma cc_T : forall (b : bool) regs m (s lines lined i wd j datas : Z) (bs : list byte) (v : word) (bt : list byte) (vt : word),
  (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i < 2 ^ 31)%Z -> (0 <= j < wd)%Z -> (wd < 2 ^ 31)%Z ->
  (1 <= lines)%Z -> (lines mod 4 = 0)%Z -> (lines + 4 * (i / 32) + 4 <= 2 ^ 64)%Z -> (1 <= datas < 2 ^ 64)%Z ->
  (1 <= lined)%Z -> (lined mod 4 = 0)%Z -> (lined + 4 * ((wd - 1 - j) / 32) + 4 <= 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (lines + 4 * (i / 32))) 4 = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  c_eq (v_andi (v_srlw (v_lw v) (v_xori (Z_to_bv 64 i) (-1))) 1) (Z_to_bv 64 0) = b ->
  rdn SEGS m (Z_to_bv 64 (lined + 4 * ((wd - 1 - j) / 32))) 4 = Some bt -> bytes_le_to_Z bt = bv_unsigned vt ->
  store_ok SEGS m (Z_to_bv 64 (lined + 4 * ((wd - 1 - j) / 32))) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 24 = Z_to_bv 64 i -> getr regs 21 = Z_to_bv 64 lines ->
  getr regs 20 = Z_to_bv 64 lined -> getr regs 23 = Z_to_bv 64 lined -> getr regs 11 = Z_to_bv 64 j ->
  getr regs 8 = Z_to_bv 64 datas -> getr regs 16 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (- 2 ^ 31) ->
  exists regs' m',
    msteps SEGS (mkst regs (Z_to_bv 64 0x97908) m rom) (mkst regs' (Z_to_bv 64 0x979e8) m' rom)
    /\ (if b then m' = m else exists wv : word, m' = wbytes m (Z_to_bv 64 (lined + 4 * ((wd - 1 - j) / 32))) (word_to_le_bytes 4 wv))
    /\ getr regs' 15 = Z_to_bv 64 lined
    /\ regs_agree (fun r => In r [9; 12; 15; 25; 26; 31]%list) regs regs'.
Proof.
  intros b regs m s lines lined i wd j datas bs v bt vt Hs Hs64 Hi Hj Hwd Hl1 Hl4 Hlb Hds Hd1 Hd4 Hdb RS LS Hb RT LT SOK RW H2 H24 H21 H20 H23 H11 H8 H16 H19.
  assert (Hi32 : (0 <= i / 32)%Z) by (apply Z.div_pos; lia).
  assert (Hw32 : (0 <= (wd - 1 - j) / 32)%Z) by (apply Z.div_pos; lia).
  assert (Hi32b : (i / 32 < 2 ^ 31)%Z) by (apply Z.div_lt_upper_bound; lia).
  assert (Hw32b : ((wd - 1 - j) / 32 < 2 ^ 31)%Z) by (apply Z.div_lt_upper_bound; lia).
  assert (Hq : ((-1 * j + (wd + -1)) / 32 = (wd - 1 - j) / 32)%Z) by (f_equal; lia).
  ex_entry regs [s; i; lines; lined; j; datas; wd; bv_swrap 32 (bv_unsigned v); bv_swrap 32 (bv_unsigned vt)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; lines; lined; j; datas; wd; bv_swrap 32 (bv_unsigned v); bv_swrap 32 (bv_unsigned vt)]) m
    [KWord (SA (EVar 32) (-108)) 4 (EVar 38); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1);
     KRange (EVar 34) 1 (2 ^ 64 - 4); KAlign (EVar 34) 4; KRange (EVar 35) 1 (2 ^ 64 - 4); KAlign (EVar 35) 4;
     KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 1 (2 ^ 64 - 1); KRange (EVar 38) 1 (2 ^ 31 - 1)]%Z) by (ex_know regs).
  destruct b.
  - cc_run 400%nat (SCR [true; true; true] [EVar 39; EVar 40] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R', m. split; [ex_mem regs Hms|]. split; [reflexivity|]. split; [v23_reg regs HR'|]. ex_agree HR HR'. }
    all: first [ cc_bit Hb | cc_rdb | cc_flat ].
  - cc_run 400%nat (SCR [true; true; false; true; true; true; true] [EVar 39; EVar 40] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R'. eexists. split; [exact Hms|]. split.
      - eexists. cbn [mem_denot]. apply ex_wbytes_eq; [reflexivity | cc_addr regs | reflexivity].
      - split; [v23_reg regs HR'|]. ex_agree HR HR'. }
    all: first [ cc_bit Hb | cc_rdb | cc_flat | cc_sok ].
Qed.

(* [comment removed for export] *)
Lemma cc_Tn : forall regs m (s i hd lined wpld : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= i)%Z -> (i + 1 < hd < 2 ^ 31)%Z -> (1 <= wpld < 2 ^ 24)%Z -> (4 * wpld < lined < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 24 = Z_to_bv 64 i -> getr regs 20 = Z_to_bv 64 lined ->
  getr regs 23 = Z_to_bv 64 lined -> getr regs 15 = Z_to_bv 64 lined -> getr regs 6 = Z_to_bv 64 (- (4 * wpld)) -> getr regs 7 = Z_to_bv 64 (- (4 * wpld)) ->
  getr regs 14 = Z_to_bv 64 (4 * wpld) -> getr regs 22 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x979e8) m rom) (mkst regs' (Z_to_bv 64 0x97908) m rom)
    /\ getr regs' 24 = Z_to_bv 64 (i + 1) /\ getr regs' 20 = Z_to_bv 64 (lined - 4 * wpld)
    /\ getr regs' 23 = Z_to_bv 64 (lined - 4 * wpld) /\ getr regs' 25 = Z_to_bv 64 hd
    /\ regs_agree (fun r => In r [12; 15; 20; 23; 24; 25; 31]%list) regs regs'.
Proof.
  intros regs m s i hd lined wpld Hs Hs64 Hi Hihd Hw Hl RH H2 H24 H20 H23 H15 H6 H7 H14 H22.
  ex_entry regs [s; i; hd; lined; (- (4 * wpld))%Z; (4 * wpld)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; hd; lined; (- (4 * wpld))%Z; (4 * wpld)%Z]) m
    [KWord (SA (EVar 32) (-112)) 4 (EVar 34); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 1);
     KRange (EVar 35) 5 (2 ^ 64 - 1); KRange (EVar 37) 4 (2 ^ 26)]%Z) by (ex_know regs).
  cc_run 400%nat (SCR [true; true; true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. repeat split; try (v23_reg regs HR'). ex_agree HR HR'. }
Qed.

Lemma cc_Tx : forall regs m (s i hd lined wpld : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= i)%Z -> (i + 1 = hd)%Z -> (hd < 2 ^ 31)%Z -> (1 <= wpld < 2 ^ 24)%Z -> (4 * wpld < lined < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 24 = Z_to_bv 64 i -> getr regs 20 = Z_to_bv 64 lined ->
  getr regs 23 = Z_to_bv 64 lined -> getr regs 15 = Z_to_bv 64 lined -> getr regs 6 = Z_to_bv 64 (- (4 * wpld)) -> getr regs 7 = Z_to_bv 64 (- (4 * wpld)) ->
  getr regs 14 = Z_to_bv 64 (4 * wpld) -> getr regs 22 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x979e8) m rom) (mkst regs' (Z_to_bv 64 0x976c4) m rom)
    /\ getr regs' 25 = Z_to_bv 64 hd
    /\ regs_agree (fun r => In r [12; 15; 20; 23; 24; 25; 31]%list) regs regs'.
Proof.
  intros regs m s i hd lined wpld Hs Hs64 Hi Hihd Hhd Hw Hl RH H2 H24 H20 H23 H15 H6 H7 H14 H22.
  ex_entry regs [s; i; hd; lined; (- (4 * wpld))%Z; (4 * wpld)%Z] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; i; hd; lined; (- (4 * wpld))%Z; (4 * wpld)%Z]) m
    [KWord (SA (EVar 32) (-112)) 4 (EVar 34); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 1);
     KRange (EVar 35) 5 (2 ^ 64 - 1); KRange (EVar 37) 4 (2 ^ 26)]%Z) by (ex_know regs).
  cc_run 400%nat (SCR [true; true; false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. repeat split; try (v23_reg regs HR'). ex_agree HR HR'. }
Qed.

(* [comment removed for export] *)
Lemma cc_Rn : forall regs m (s j wd : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= j)%Z -> (j + 1 < wd < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 11 = Z_to_bv 64 j ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x976c4) m rom) (mkst regs' (Z_to_bv 64 0x976d4) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (j + 1) /\ getr regs' 9 = Z_to_bv 64 wd
    /\ regs_agree (fun r => In r [9; 11]%list) regs regs'.
Proof.
  intros regs m s j wd Hs Hs64 Hj Hwd RW H2 H11.
  ex_entry regs [s; j; wd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; j; wd]) m
    [KWord (SA (EVar 32) (-108)) 4 (EVar 34); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs).
  cc_run 400%nat (SCR [true] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. repeat split; try (v23_reg regs HR'). ex_agree HR HR'. }
Qed.

Lemma cc_Rx : forall regs m (s j wd : Z), (192 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= j)%Z -> (j + 1 = wd)%Z -> (wd < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 wd)) ->
  getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 11 = Z_to_bv 64 j ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 0x976c4) m rom) (mkst regs' (Z_to_bv 64 0x98a2c) m rom)
    /\ regs_agree (fun r => In r [9; 11]%list) regs regs'.
Proof.
  intros regs m s j wd Hs Hs64 Hj Hjw Hwd RW H2 H11.
  ex_entry regs [s; j; wd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; j; wd]) m
    [KWord (SA (EVar 32) (-108)) 4 (EVar 34); KRange (EVar 32) 192 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 31 - 1); KRange (EVar 34) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs).
  cc_run 400%nat (SCR [false] [] []) HR HK R' HR' Hms.
  all: cycle -1.
  { exists R'. split; [ex_mem regs Hms|]. ex_agree HR HR'. }
Qed.

End SegsT.
