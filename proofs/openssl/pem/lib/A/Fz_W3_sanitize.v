(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_env Fz_W1_defs Fz_W3_iface Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CTYPE_TAB : Z := 0x4b320.     (* [comment removed for export] *)
Definition LIT_BOM : Z := 0xa1ca0.       (* [comment removed for export] *)
Definition e_ossl_ctype_check : Z := 0x20411c.
Definition SITE_san_mcmp : Z := 0x30ce6c. (* [comment removed for export] *)
Definition SITE_san_mmv : Z := 0x30ce88.  (* [comment removed for export] *)
Definition J_DISP : Z := 0x30cea0.        (* [comment removed for export] *)
Definition J_DFL : Z := 0x30ced0.         (* [comment removed for export] *)
Definition J_EAY : Z := 0x30cf44.         (* [comment removed for export] *)
Definition J_B64 : Z := 0x30cf88.         (* [comment removed for export] *)
Definition J_TAIL : Z := 0x30d008.        (* [comment removed for export] *)

Definition ctype_table : list byte := Eval vm_compute in (match image_bytes asegs CTYPE_TAB 256 with Some bs => bs | None => [] end).
Lemma ctype_table_len : length ctype_table = 256%nat.
Proof. reflexivity. Qed.
Lemma ctype_table_at : forall m : mem, mem_inv asegs m -> bytes_at asegs m CTYPE_TAB ctype_table.
Proof.
  intros m HI.
  assert (RO : ro_cells asegs m CTYPE_TAB [CB 256 ctype_table])
    by (apply (ro_cells_image asegs m CTYPE_TAB ctype_table HI); [vm_compute; reflexivity | unfold CTYPE_TAB; lia | cbn; unfold CTYPE_TAB; lia]).
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Definition bom_lit : list byte := Eval vm_compute in (match image_bytes asegs LIT_BOM 3 with Some bs => bs | None => [] end).
Lemma bom_lit_len : length bom_lit = 3%nat.
Proof. reflexivity. Qed.
Lemma bom_lit_at : forall m : mem, mem_inv asegs m -> bytes_at asegs m LIT_BOM bom_lit.
Proof.
  intros m HI.
  assert (RO : ro_cells asegs m LIT_BOM [CB 3 bom_lit]) by (apply (ro_cells_image asegs m LIT_BOM bom_lit HI); [vm_compute; reflexivity | unfold LIT_BOM; lia | cbn; unfold LIT_BOM; lia]).
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ctype_post (ra sp gp tp t0 t1 t2 a1 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (r : Z) (a2' a3' a4' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ (r = 0 \/ r = 1) /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma ctype_check_proof : forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c mask lo : Z),
  a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 mask -> 0 <= c < 256 -> 0 <= mask < 2 ^ 32 ->
  lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] -> acc asegs m CTYPE_TAB 256 -> mem_inv asegs m ->
  evt asegs (ctype_post ra sp gp (wz TP_A) t0 t1 t2 a1 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_ossl_ctype_check) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> Hc Hm HLO HLOS SPH ST UT SHC ACT MI. unfold e_ossl_ctype_check, TP_A, SHB, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 16, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 16, SP)]) by sh_fp_lia.
  assert (CTAL : CTYPE_TAB mod 8 = 0) by reflexivity. unfold CTYPE_TAB in ACT, CTAL.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 zstep.
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    zstep. zstep. zstep. th_release FR SP. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned. change Startup_glue.z64 with (Z_to_bv 64 0).
    apply evt_done. unfold ctype_post. exists 0. do 4 eexists. split; [reflexivity|]. split; [left; reflexivity|].
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia. auto.
  - zstep. zstep. zstep. try rewrite (Z.shiftl_mul_pow2 c 1) by lia. change (2 ^ 1) with 2. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep.
    if_false.
    pose proof (bytes_at_read asegs m1 CTYPE_TAB ctype_table (2 * c) 2 (ctype_table_at m1 MI) ltac:(lia) ltac:(rewrite ctype_table_len; lia)) as RD.
    replace (wa (CTYPE_TAB + 2 * c)) with (Z_to_bv 64 (308000 + c * 2)) in RD by (unfold wa, CTYPE_TAB; f_equal; lia).
    zstep. zstep. clear RD. zstep. zstep. zstep. zstep. th_release FR SP. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    apply evt_done. unfold ctype_post.
    lazymatch goal with |- context [Z_to_bv 64 (Z.b2z ?b)] => exists (Z.b2z b); do 4 eexists; split; [reflexivity|]; split; [destruct b; cbn [Z.b2z]; [right| left]; reflexivity|] end.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia. auto.
Qed.
Lemma t_le1_word : forall w : word, le1 w = [Z_to_bv 8 (bv_unsigned w mod 256)].
Proof. intros w. rewrite <- (Z_to_bv_bv_unsigned w) at 1. apply th_le1_mod. Qed.

Lemma swrap32_small : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma san_signed_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z H. rewrite ZBridge.zb_signed, unsigned_lit by lia. replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SanA.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (mD : mem) (LB clen lo : Z) (bsD : list byte) (j0 : list byte).
  Let SP : Z := bv_unsigned sp.
  Definition san_W : list (Z * Z) := [(LB, LB + 256); (SP - 128, SP)].
  Definition san_frame : list cell := [CB 8 j0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis AB : 0 < LB /\ 0x10007fff8000 <= LB /\ LB + 256 <= lo /\ 0x10007fff8000 <= lo /\ lo <= SP - 128 /\ SP <= 2 ^ 47 /\ LB mod 16 = 0 /\ 1 <= clen <= 254 /\ length j0 = 8%nat.
  Hypothesis LBAL8 : LB mod 8 = 0.
  Hypothesis UTD : img_untouched mD.
  Hypothesis SHCD : ro_cells asegs mD g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)].
  Hypothesis ACLD : acc asegs mD LB 256.
  Hypothesis ACTD : acc asegs mD CTYPE_TAB 256.

  Lemma san_W_sh : sh_fp san_W.
  Proof. unfold san_W. clear - AB. sh_fp_lia. Qed.
  Lemma san_W_ut : ut_fp san_W.
  Proof. unfold san_W. clear - AB. ut_fp_lia. Qed.

  Definition LFD : Prop := nth_error bsD (Z.to_nat (clen - 1)) = Some (Z_to_bv 8 10).

  Definition sanitize_postA : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (len' : Z) (bs' : list byte) (m' : mem),
       ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 len') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ 1 <= len' <= clen + 1 /\ (LFD -> len' <= clen)
    /\ munch san_W mD m' /\ wmono asegs mD m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
    /\ length bs' = 256%nat /\ rw_cells asegs m' LB [CB 256 bs']
    /\ nth_error bs' (Z.to_nat (len' - 1)) = Some (Z_to_bv 8 10) /\ nth_error bs' (Z.to_nat len') = Some (Z_to_bv 8 0).
  Notation POST := sanitize_postA.
  (* [comment removed for export] *)
  Notation ST pc mm xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 y3 y5 y6 y7 y8 y9 y10 y11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SP + -112)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 LB) x10 x11 x12 x13 x14 x15 x16 x17 y2 y3 (Z_to_bv 64 SHB) y5 y6 y7 y8 y9 y10 y11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition INVb (mX : mem) (bs : list byte) : Prop :=
    u8arr asegs mX LB bs /\ length bs = 256%nat
    /\ rw_cells asegs mX (SP + -112) san_frame /\ stk asegs mX lo (SP + -112)
    /\ mem_inv asegs mX /\ munch san_W mD mX /\ wmono asegs mD mX.
  Ltac open_inv H := destruct H as (DST & LBS & FR & ST & MI & MU & WM).

  Lemma invb_store_ok : forall mX bs k a, INVb mX bs -> 0 <= k <= 255 -> a = wa (LB + k) -> store_ok asegs mX a 1 = true.
  Proof. intros mX bs k a I Hk Ha; open_inv I. eapply (u8arr_store_ok asegs mX LB bs k a DST); [rewrite LBS; lia | exact Ha]. Qed.

  Lemma invb_store : forall mX bs k a b, INVb mX bs -> 0 <= k <= 255 -> a = wa (LB + k) -> INVb (write_to_mem mX a [b]) (upd bs (Z.to_nat k) b).
  Proof.
    intros mX bs k a b I Hk Ha. pose proof (invb_store_ok mX bs k a I Hk Ha) as SOK. open_inv I. subst a.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - apply (u8arr_write asegs mX LB bs k b DST). rewrite LBS. lia.
    - rewrite upd_length. exact LBS.
    - apply rw_cells_frame; [exact FR | unfold SP in *; lia | cbn [length]; lia | unfold san_frame; cbn [length cells_size csize Nat.add]; unfold SP in *; lia].
    - apply stk_write; [exact ST | lia | cbn [length]; unfold SP in *; lia].
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU | lia | cbn [length]; lia |]. unfold san_W. cbn [inside length]. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma invb_call : forall mX mX' bs, INVb mX bs -> munch [(SP + -112 - 16, SP + -112)]%Z mX mX' -> wmono asegs mX mX' -> mem_inv asegs mX' -> stk asegs mX' lo (SP + -112) ->
    INVb mX' bs.
  Proof.
    intros mX mX' bs I MU' WM' MI' ST'; open_inv I.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply u8arr_transport; [exact DST| exact MU'| exact WM'|]. rewrite LBS. cbn [disjoint_from]. unfold SP in *; lia.
    - exact LBS.
    - eapply rw_cells_transport; [exact FR| exact MU'| exact WM'|]. unfold san_frame. cbn [disjoint_from cells_size csize Nat.add]. lia.
    - exact ST'.
    - exact MI'.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, san_W. cbn [outside]. intros a Ha. unfold SP in *; lia.
    - eapply wmono_trans; [exact WM| exact WM'].
  Qed.

  (* [comment removed for export] *)
  Lemma invb_ut : forall mX bs, INVb mX bs -> img_untouched mX.
  Proof. intros mX bs I; open_inv I. exact (ut_munch san_W mD mX UTD MU san_W_ut). Qed.
  Lemma invb_shc : forall mX bs, INVb mX bs -> ro_cells asegs mX g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)].
  Proof. intros mX bs I; open_inv I. eapply ro_cells_transport; [exact SHCD| exact MU|]. unfold san_W, g_shadow_memory_dynamic_address. cbn [disjoint_from cells_size csize Nat.add]. unfold SP in *; lia. Qed.
  Lemma invb_act : forall mX bs, INVb mX bs -> acc asegs mX CTYPE_TAB 256.
  Proof. intros mX bs I; open_inv I. exact (acc_munch_sh san_W mD mX CTYPE_TAB 256 ACTD MU san_W_sh ltac:(unfold CTYPE_TAB; lia) ltac:(unfold CTYPE_TAB; lia)). Qed.

  (* [comment removed for export] *)
  Ltac drop_open := repeat match goal with
    | H : u8arr asegs _ LB _ |- _ => clear H
    | H : length _ = 256%nat |- _ => clear H
    | H : rw_cells asegs _ (SP + -112) _ |- _ => clear H
    | H : stk asegs _ lo _ |- _ => clear H
    | H : mem_inv asegs _ |- _ => clear H
    | H : munch san_W mD _ |- _ => clear H
    | H : wmono asegs mD _ |- _ => clear H
    end.
  Ltac reopen I := drop_open; let I0 := fresh "I0" in pose proof I as I0; destruct I0 as (DST & LBS & FR & STK & MI & MU & WM); unfold san_frame in FR.

  (* [comment removed for export] *)
  Ltac stb I k ADDR :=
    lazymatch type of I with INVb ?mX ?bs =>
      reopen I;
      let SOK := fresh "SOK" in
      pose proof (invb_store_ok mX bs k (Z_to_bv 64 ADDR) I ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      zstep; clear SOK;
      rewrite t_le1_word;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?b]) _) =>
        let I2 := fresh "I" in
        pose proof (invb_store mX bs k (Z_to_bv 64 ADDR) b I ltac:(lia) ltac:(unfold wa; f_equal; lia)) as I2;
        drop_open;
        let m2 := fresh "m" in
        remember (write_to_mem mX (Z_to_bv 64 ADDR) [b]) as m2 eqn:Em; clear Em;
        clear I; try clear mX; rename I2 into I; reopen I
      end
    end.

  (* [comment removed for export] *)
  Ltac ldb I k ADDR b Hb :=
    lazymatch type of I with INVb ?mX ?bs =>
      destruct (nth_error bs (Z.to_nat k)) as [b|] eqn:Hb;
      [| exfalso; apply nth_error_None in Hb; pose proof I as (_ & ? & _); lia];
      let RD := fresh "RD" in
      pose proof (u8arr_read asegs mX LB bs k b (Z_to_bv 64 ADDR) ltac:(pose proof I as (? & _); assumption) Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      zstep; clear RD
    end.

  (* [comment removed for export] *)
  Lemma san_tail : forall mX bs i xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 y3 y6 y7 y8 y9 y10 y11 x28 x29 x30 x31,
    INVb mX bs -> 0 <= i <= clen -> (LFD -> i <= clen - 1) ->
    evt asegs POST (ST J_TAIL mX xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y2 y3 (Z_to_bv 64 i) y6 y7 y8 y9 y10 y11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I Hi HLF. unfold J_TAIL, TP_A, SHB. pose proof san_W_sh as HWS. pose proof san_W_ut as HWU.
    reopen I.
    zstep. zstep. zstep. zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
    zstep. rewrite (swrap32_small (i + 1)) by lia. zstep.
    stb I i (LB + i).
    zstep. zstep. zstep. zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
    stb I (i + 1) (LB + (i + 1)).
    do 13 zstep. th_release FR SP. zstep. zstep.
    change (Z_to_bv 64 SP) with (Z_to_bv 64 (bv_unsigned sp)). rewrite Z_to_bv_bv_unsigned.
    rewrite ?unsigned_lit in DST, LBS by lia. change Startup_glue.z64 with (Z_to_bv 64 0) in DST, LBS. rewrite ?unsigned_lit in DST, LBS by lia.
    change (10 mod 256) with 10 in DST, LBS. change (0 mod 256) with 0 in DST, LBS.
    apply evt_done. unfold sanitize_postA. do 14 eexists. exists (i + 1). do 2 eexists.
    split; [reflexivity|]. split; [lia|]. split; [intros H; specialize (HLF H); lia|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact LBS|].
    split; [pose proof (rw_cells_of_u8arr asegs _ _ _ DST) as X; rewrite LBS in X; exact X|].
    rewrite upd_length in LBS. rewrite upd_length in LBS.
    replace (Z.to_nat (i + 1 - 1)) with (Z.to_nat i) by lia.
    split; [rewrite nth_error_upd_other by lia; apply nth_error_upd_same; rewrite LBS; lia| apply nth_error_upd_same; rewrite upd_length, LBS; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma san_eay : forall (k : nat) j mX bs xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 y3 y5 y6 y7 y8 y9 y10 y11 x28 x29 x30 x31,
    INVb mX bs -> j = Z.of_nat k -> j <= clen -> nth_error bs (Z.to_nat clen) = Some (Z_to_bv 8 0) ->
    nth_error bs (Z.to_nat (clen - 1)) = nth_error bsD (Z.to_nat (clen - 1)) ->
    evt asegs POST (ST J_EAY mX xra x5 x6 x7 x10 (Z_to_bv 64 32) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 j) y3 y5 y6 y7 y8 y9 y10 y11 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I Hj Hjc NUL HBD; unfold J_EAY, TP_A, SHB; pose proof san_W_sh as HWS; pose proof san_W_ut as HWU.
    - subst j. change (Z.of_nat 0) with 0. reopen I.
      zstep. zstep. zstep. zstep. zstep.
      cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      ldb I 0 LB b Hb. cbv beta.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep.
      if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        assert (C0 : 0 < clen).
        { destruct (Z.eq_dec clen 0) as [E|]; [| lia]. exfalso. rewrite E in NUL. cbn [Z.to_nat] in NUL. rewrite NUL in Hb. inversion Hb; subst. change (bv_unsigned (Z_to_bv 8 0)) with 0 in K0. lia. }
        zstep. zstep.
        eapply san_tail; [exact I| lia|].
        intros HL. destruct (Z.eq_dec clen 1) as [E1|]; [| lia]. exfalso. unfold LFD in HL. rewrite <- HBD in HL. rewrite E1 in HL.
        change (Z.to_nat (1 - 1)) with (Z.to_nat 0) in HL. rewrite HL in Hb. inversion Hb; subst. change (bv_unsigned (Z_to_bv 8 10)) with 10 in K0. lia.
      + zstep. zstep. th_if_lit. zstep. zstep. zstep. zstep.
        change Startup_glue.z64 with (Z_to_bv 64 0). eapply san_tail; [exact I| lia| intros; lia].
    - reopen I.
      zstep. zstep. zstep. zstep. zstep.
      cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      ldb I j (LB + j) b Hb. cbv beta.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. if_cases K0; zify_cond K0.
      + assert (C0 : j < clen).
        { destruct (Z.eq_dec j clen) as [E|]; [| lia]. exfalso. rewrite <- E in NUL. rewrite NUL in Hb. inversion Hb; subst. change (bv_unsigned (Z_to_bv 8 0)) with 0 in K0. lia. }
        zstep. rewrite (swrap32_small (j + 1)) by lia. zstep.
        eapply san_tail; [exact I| lia|].
        intros HL. destruct (Z.eq_dec j (clen - 1)) as [E1|]; [| lia]. exfalso. unfold LFD in HL. rewrite <- HBD in HL. rewrite <- E1 in HL.
        rewrite HL in Hb. inversion Hb; subst. change (bv_unsigned (Z_to_bv 8 10)) with 10 in K0. clear IH. lia.
      + zstep. rewrite (swrap32_small (j + -1)) by lia. zstep. if_cases K1; zify_cond K1. 2: { exfalso. clear IH. lia. }
        replace (j + -1) with (Z.of_nat k) by (clear IH; lia). eapply IH; [exact I| reflexivity| clear IH; lia | exact NUL| exact HBD].
  Qed.

  (* [comment removed for export] *)
  Ltac call_ctypeA I :=
    lazymatch type of I with INVb ?mX ?bs =>
      drop_open;
      eapply evt_cut;
      [ eapply ctype_check_proof with (lo := lo);
        [ reflexivity | reflexivity | lia | lia
        | rewrite unsigned_lit by lia; lia | lia | rewrite unsigned_lit by lia; lia
        | rewrite !unsigned_lit by lia; replace (SP + -112 - 16) with (SP + -112 + -16) by lia; pose proof I as (_ & _ & _ & ? & _); assumption
        | exact (invb_ut _ _ I) | exact (invb_shc _ _ I) | exact (invb_act _ _ I)
        | pose proof I as (_ & _ & _ & _ & ? & _); assumption ]
      | let ms' := fresh "ms'" in let PO := fresh "PO" in let I2 := fresh "I" in
        intros ms' PO; unfold ctype_post in PO; rewrite !unsigned_lit in PO by lia;
        destruct PO as (?r & ?a2' & ?a3' & ?a4' & ?mY & -> & ?Hr & MU' & WM' & MI' & ST');
        pose proof (invb_call _ _ _ I MU' WM' MI' ST') as I2; clear I MU' WM' MI' ST'; rename I2 into I; th_ret_lit; reopen I ]
    end.

  (* [comment removed for export] *)
  Lemma san_b64 : forall (k : nat) i P rem mX bs xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y10 y11 x28 x29 x30 x31,
    INVb mX bs -> 0 <= i -> i + Z.of_nat (S k) = clen -> P = LB + i -> rem = Z.of_nat (S k) ->
    nth_error bs (Z.to_nat (clen - 1)) = nth_error bsD (Z.to_nat (clen - 1)) ->
    evt asegs POST (ST J_B64 mX xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 rem)
                       (Z_to_bv 64 10) (Z_to_bv 64 13) (Z_to_bv 64 P) y10 y11 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I Hi Hk HP Hrem HBD; unfold J_B64, TP_A, SHB; pose proof san_W_sh as HWS; pose proof san_W_ut as HWU; subst P rem.
    - change (Z.of_nat 1) with 1 in *. reopen I.
      zstep. zstep. zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      ldb I i (LB + i) b Hb. cbv beta. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. zstep. call_ctypeA I.
      zstep.
      if_cases K0; zify_cond K0. { eapply san_tail; [exact I| lia| clear -Hk; intros; lia]. }
      zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      ldb I i (LB + i) b2 Hb2. cbv beta. assert (Eb : b2 = b) by congruence. subst b2. clear Hb. rename Hb2 into Hb.
      zstep. if_cases K1; zify_cond K1. { eapply san_tail; [exact I| lia| clear - Hk; intros; lia]. }
      zstep. if_cases K2; zify_cond K2. { eapply san_tail; [exact I| lia| clear - Hk; intros; lia]. }
      zstep. rewrite (swrap32_small (i + 1)) by lia. zstep. zstep. zstep. zstep. th_if_lit. zstep. zstep.
      eapply san_tail; [exact I| lia|].
      intros HL. exfalso. unfold LFD in HL. rewrite <- HBD in HL. replace (clen - 1) with i in HL by lia. rewrite HL in Hb. inversion Hb; subst.
      change (bv_unsigned (Z_to_bv 8 10)) with 10 in K1. lia.
    - reopen I.
      zstep. zstep. zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      ldb I i (LB + i) b Hb. cbv beta. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. zstep. call_ctypeA I.
      zstep. if_cases K0; zify_cond K0. { eapply san_tail; [exact I| clear IH; lia| clear -Hk; intros; lia]. }
      zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      ldb I i (LB + i) b2 Hb2. cbv beta. assert (Eb : b2 = b) by congruence. subst b2. clear Hb. rename Hb2 into Hb.
      zstep. if_cases K1; zify_cond K1. { eapply san_tail; [exact I| clear IH; lia| clear - Hk; intros; lia]. }
      zstep. if_cases K2; zify_cond K2. { eapply san_tail; [exact I| clear IH; lia| clear - Hk; intros; lia]. }
      zstep. rewrite (swrap32_small (i + 1)) by (clear IH; lia). zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3. 2: { exfalso. clear IH. lia. }
      replace (LB + i + 1) with (LB + (i + 1)) by lia. replace (Z.of_nat (S (S k)) + -1) with (Z.of_nat (S k)) by (clear IH; lia).
      eapply IH; [exact I| clear IH; lia| clear IH; lia| reflexivity| reflexivity| exact HBD].
  Qed.

  (* [comment removed for export] *)
  Lemma san_dflt : forall (k : nat) i P rem mX bs xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y11 x28 x29 x30 x31,
    INVb mX bs -> 0 <= i -> i + Z.of_nat (S k) = clen -> P = LB + i -> rem = Z.of_nat (S k) ->
    nth_error bs (Z.to_nat (clen - 1)) = nth_error bsD (Z.to_nat (clen - 1)) ->
    evt asegs POST (ST J_DFL mX xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 rem)
                       (Z_to_bv 64 10) (Z_to_bv 64 13) (Z_to_bv 64 32) (Z_to_bv 64 P) y11 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I Hi Hk HP Hrem HBD; unfold J_DFL, TP_A, SHB; pose proof san_W_sh as HWS; pose proof san_W_ut as HWU; subst P rem.
    - change (Z.of_nat 1) with 1 in *. reopen I.
      zstep. zstep. zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      ldb I i (LB + i) b Hb. cbv beta. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. if_cases K1; zify_cond K1. { eapply san_tail; [exact I| lia| clear - Hk; intros; lia]. }
      zstep. if_cases K2; zify_cond K2. { eapply san_tail; [exact I| lia| clear - Hk; intros; lia]. }
      assert (NLF : ~ LFD).
      { intros HL. unfold LFD in HL. rewrite <- HBD in HL. replace (clen - 1) with i in HL by lia. rewrite HL in Hb. inversion Hb; subst. change (bv_unsigned (Z_to_bv 8 10)) with 10 in K1. lia. }
      (* [comment removed for export] *)
      drop_open.
      assert (J : forall mZ bsZ z10 z11 z12 z13 z14 z20, INVb mZ bsZ ->
        evt asegs POST (ST 0x30cf08 mZ (Z_to_bv 64 0x30cef8) x5 x6 x7 z10 z11 z12 z13 z14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 (LB + i)) (Z_to_bv 64 i) (Z_to_bv 64 1)
                           (Z_to_bv 64 10) (Z_to_bv 64 13) (Z_to_bv 64 32) (Z_to_bv 64 (LB + i)) z20 x28 x29 x30 x31)).
      { intros mZ bsZ z10 z11 z12 z13 z14 z20 IZ. reopen IZ. zstep. rewrite (swrap32_small (i + 1)) by lia. zstep. zstep. zstep. zstep. th_if_lit. zstep.
        eapply san_tail; [exact IZ| lia| intros HL; exfalso; exact (NLF HL)]. }
      reopen I. zstep. zstep. call_ctypeA I.
      zstep. if_cases K0; zify_cond K0. { eapply J; exact I. }
      zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      stb I i (LB + i). eapply J; exact I.
    - assert (J : forall mZ bsZ z10 z11 z12 z13 z14 z20, INVb mZ bsZ -> nth_error bsZ (Z.to_nat (clen - 1)) = nth_error bsD (Z.to_nat (clen - 1)) ->
        evt asegs POST (ST 0x30cf08 mZ (Z_to_bv 64 0x30cef8) x5 x6 x7 z10 z11 z12 z13 z14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 (LB + i)) (Z_to_bv 64 i) (Z_to_bv 64 (Z.of_nat (S (S k))))
                           (Z_to_bv 64 10) (Z_to_bv 64 13) (Z_to_bv 64 32) (Z_to_bv 64 (LB + i)) z20 x28 x29 x30 x31)).
      { intros mZ bsZ z10 z11 z12 z13 z14 z20 IZ HBZ. reopen IZ. zstep. rewrite (swrap32_small (i + 1)) by (clear IH; lia). zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear IH. lia. }
        zstep. replace (LB + i + 1) with (LB + (i + 1)) by lia. replace (Z.of_nat (S (S k)) + -1) with (Z.of_nat (S k)) by (clear IH; lia).
        eapply IH; [exact IZ| clear IH; lia| clear IH; lia| reflexivity| reflexivity| exact HBZ]. }
      reopen I.
      zstep. zstep. zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      ldb I i (LB + i) b Hb. cbv beta. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
      zstep. if_cases K1; zify_cond K1. { eapply san_tail; [exact I| clear IH; lia| clear - Hk; intros; lia]. }
      zstep. if_cases K2; zify_cond K2. { eapply san_tail; [exact I| clear IH; lia| clear - Hk; intros; lia]. }
      zstep. zstep. call_ctypeA I.
      zstep. if_cases K0; zify_cond K0. { eapply J; [exact I | exact HBD]. }
      zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
      stb I i (LB + i). eapply J; [exact I |]. rewrite nth_error_upd_other by (clear IH; lia). exact HBD.
  Qed.

  (* [comment removed for export] *)
  Lemma san_dispatch : forall flags mX bs xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 y5 y6 y7 y8 y9 y10 y11 x28 x29 x30 x31,
    INVb mX bs -> 0 <= flags < 2 ^ 32 -> nth_error bs (Z.to_nat clen) = Some (Z_to_bv 8 0) ->
    nth_error bs (Z.to_nat (clen - 1)) = nth_error bsD (Z.to_nat (clen - 1)) ->
    evt asegs POST (ST J_DISP mX xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 clen) (Z_to_bv 64 flags) y5 y6 y7 y8 y9 y10 y11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HF NUL HBD. unfold J_DISP, TP_A, SHB. pose proof san_W_sh as HWS. pose proof san_W_ut as HWU. reopen I.
    zstep. zstep. if_cases KE; zify_cond KE.
    - zstep. eapply (san_eay (Z.to_nat clen) clen); [exact I| lia| lia| exact NUL| exact HBD].
    - zstep. zstep. zstep. replace (Z.land clen 4294967295) with clen by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones, Z.mod_small by lia; lia).
      zstep. zstep. zstep. zstep. if_cases KB; zify_cond KB.
      + zstep. zstep. eapply (san_b64 (Z.to_nat (clen - 1)) 0 LB); [exact I| lia| lia| lia| lia| exact HBD].
      + zstep. zstep. zstep. eapply (san_dflt (Z.to_nat (clen - 1)) 0 LB); [exact I| lia| lia| lia| lia| exact HBD].
  Qed.
End SanA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition san_saved (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma rw_CB_hd_len : forall (m : mem) A n bs cs, rw_cells asegs m A (CB n bs :: cs) -> length bs = n.
Proof. intros m A n bs cs [[[H _] _] _]. exact H. Qed.

(* [comment removed for export] *)
Definition w0_post (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (LB len flags fcall lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j : list byte) (m' : mem),
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - 112)
    /\ rw_cells asegs m' (bv_unsigned sp + -112) (CB 8 j :: san_saved s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) /\ length j = 8%nat
    /\ ( ((fcall = 0 \/ len < 4) /\ exists a0 a1 a2 : word,
             ms = MS (mkR ra (wz (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (wz LB) a0 a1 a2 (wz fcall) a4 a5 a6 a7 (wz len) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz J_DISP) fc None m' (seg_rom asegs))
      \/ ((fcall <> 0 /\ 4 <= len)
          /\ ms = MS (mkR (wz SITE_san_mcmp) (wz (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (wz LB) (wz LB) (wz LIT_BOM) (wz 3) (wz fcall) a4 a5 a6 a7 (wz len) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz e_memcmp) fc None m' (seg_rom asegs)) ).

Lemma w0_walk : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (LB len flags fcall lo : Z),
  lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  0 < LB -> LB + 256 <= lo -> 1 <= len <= 254 -> 0 <= flags < 2 ^ 32 -> 0 <= fcall < 2 ^ 32 -> mem_inv asegs m ->
  evt asegs (w0_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB len flags fcall lo m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz LB) (wz len) (wz flags) (wz fcall) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_SANITIZE) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT SHC LB0 LBLO HL HF HC MI. unfold FZ_SANITIZE, TP_A, SHB, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 112, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 112, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 112, SP)]) by sh_fp_lia.
  th_frame 112%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 13 zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. if_cases K0; zify_cond K0.
  - subst SP. rewrite ?Z_to_bv_bv_unsigned. apply evt_done. unfold w0_post, J_DISP, san_saved. cbv beta. do 13 eexists.
    split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia; assumption|]. split; [eassumption|]. split; [eapply rw_CB_hd_len; eassumption|].
    left. split; [left; exact K0| do 3 eexists; reflexivity].
  - zstep. zstep. if_cases K1; zify_cond K1.
    + subst SP. rewrite ?Z_to_bv_bv_unsigned. apply evt_done. unfold w0_post, J_DISP, san_saved. cbv beta. do 13 eexists.
      split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia; assumption|]. split; [eassumption|]. split; [eapply rw_CB_hd_len; eassumption|].
      left. split; [right; rewrite ?unsigned_lit in K1 by lia; exact K1| do 3 eexists; reflexivity].
    + zstep. zstep. zstep. zstep. zstep.
      subst SP. rewrite ?Z_to_bv_bv_unsigned. apply evt_done. unfold w0_post, SITE_san_mcmp, e_memcmp, LIT_BOM, san_saved. cbv beta. do 13 eexists.
      split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia; assumption|]. split; [eassumption|]. split; [eapply rw_CB_hd_len; eassumption|].
      right. split; [rewrite ?unsigned_lit in K1 by lia; split; [exact K0| lia]| reflexivity].
Qed.

Lemma memcmp_res_range : forall b1 b2, -256 < memcmp_res b1 b2 < 256.
Proof.
  induction b1 as [|x b1 IH]; intros [|y b2]; cbn [memcmp_res]; try lia.
  pose proof (bv_unsigned_in_range 8 x) as Rx. pose proof (bv_unsigned_in_range 8 y) as Ry. unfold bv_modulus in Rx, Ry. change (2 ^ Z.of_N 8) with 256 in Rx, Ry.
  destruct (bv_unsigned x =? bv_unsigned y); [apply IH| lia].
Qed.
Lemma san_mv_cur_length : forall off bs i, (off + i <= length bs)%nat -> length (mv_cur off bs i) = length bs.
Proof. intros off bs i H. unfold mv_cur. rewrite length_app, length_firstn, !length_skipn. lia. Qed.

Lemma land64_zero_small : forall r, -256 < r < 256 -> Z.land r 18446744073709551615 = 0 -> r = 0.
Proof.
  intros r Hr H. change 18446744073709551615 with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z_lt_ge_dec r 0) as [N|N].
  - replace r with ((r + 2 ^ 64) + (-1) * 2 ^ 64) in H by lia. rewrite Z.mod_add in H by lia. rewrite Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma w1_walk : forall (gp : word) t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (LB len flags r usp1 : Z),
  4 <= len <= 254 -> -256 < r < 256 -> 0 < LB -> LB + 256 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms =>
       (r <> 0 /\ ms = MS (mkR (wz SITE_san_mcmp) (wz usp1) gp (wz TP_A) t0 t1 t2 s0 (wz LB) (wz r) a1 a2 a3 a4 a5 a6 a7 (wz len) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz J_DISP) fc None m (seg_rom asegs))
    \/ (r = 0 /\ ms = MS (mkR (wz SITE_san_mmv) (wz usp1) gp (wz TP_A) t0 t1 t2 s0 (wz LB) (wz LB) (wz (LB + 3)) (wz (len - 3)) a3 a4 a5 a6 a7 (wz (len - 3)) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz e_asan_memmove) fc None m (seg_rom asegs)))
    (MS (mkR (wz SITE_san_mcmp) (wz usp1) gp (wz TP_A) t0 t1 t2 s0 (wz LB) (wz r) a1 a2 a3 a4 a5 a6 a7 (wz len) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc (wz SITE_san_mcmp)) fc None m (seg_rom asegs)).
Proof.
  intros until usp1. intros HL HR LB0 LBT MI. unfold SITE_san_mcmp, TP_A, SHB in *. rewrite (ret_pc_even 3198572) by lia.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_cases K0; zify_cond K0.
  - apply evt_done. left. split; [| unfold J_DISP; reflexivity]. intros ->. apply K0. reflexivity.
  - zstep.
    zstep. rewrite (swrap32_small (len + -3)) by lia. replace (len + -3) with (len - 3) by lia. zstep. zstep. zstep.
    apply evt_done. right. split; [exact (land64_zero_small r HR K0)| unfold SITE_san_mmv, e_asan_memmove; reflexivity].
Qed.

(* [comment removed for export] *)
Definition w2_post (sp gp s0 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (LB len flags lo : Z) (bs : list byte) (fr : list cell) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (a1 : word) (m' : mem),
    ms = MS (mkR (wz SITE_san_mmv) (wz (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 s0 (wz LB) (wz (LB + (len - 3))) a1 a2 a3 a4 a5 a6 a7 (wz (len - 3)) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz J_DISP) fc None m' (seg_rom asegs)
    /\ munch [(LB + (len - 3), LB + (len - 3) + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -112)
    /\ rw_cells asegs m' (bv_unsigned sp + -112) fr /\ u8arr asegs m' LB (upd bs (Z.to_nat (len - 3)) (Z_to_bv 8 0)).
Lemma w2_walk : forall sp gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (LB len flags lo : Z) (bs : list byte) (fr : list cell),
  4 <= len <= 254 -> 0 < LB -> 0x10007fff8000 <= LB -> LB + 256 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 -> LB mod 8 = 0 ->
  u8arr asegs m LB bs -> length bs = 256%nat -> acc asegs m LB 256 ->
  rw_cells asegs m (bv_unsigned sp + -112) fr -> cells_size fr = 112%nat -> stk asegs m lo (bv_unsigned sp + -112) -> mem_inv asegs m ->
  evt asegs (w2_post sp gp s0 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc LB len flags lo bs fr m)
    (MS (mkR (wz SITE_san_mmv) (wz (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 s0 (wz LB) (wz LB) a1 a2 a3 a4 a5 a6 a7 (wz (len - 3)) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc (wz SITE_san_mmv)) fc None m (seg_rom asegs)).
Proof.
  intros until fr. intros HL LB0 LBHI LBLO HLO SPH LBAL8 DST LBS ACL FR FRS ST MI. unfold SITE_san_mmv, TP_A, SHB in *. rewrite (ret_pc_even 3198600) by lia.
  pose proof (munch_refl [(LB + (len - 3), LB + (len - 3) + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWS : sh_fp [(LB + (len - 3), LB + (len - 3) + 1)]) by sh_fp_lia.
  zstep. zstep. zstep. zstep. cbv beta; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
  pose proof (u8arr_store_ok asegs m LB bs (len - 3) (Z_to_bv 64 (LB + (len - 3))) DST ltac:(rewrite LBS; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep. clear SOK.
  change (le1 Startup_glue.z64) with [Z_to_bv 8 0].
  apply evt_done. unfold w2_post, J_DISP. do 2 eexists. split; [reflexivity|].
  split; [apply munch_write; [exact MU | lia | cbn [length]; lia |]; cbn [inside length]; left; lia|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI|]; eapply (u8arr_store_ok asegs m LB bs (len - 3) _ DST); [rewrite LBS; lia| unfold wa; f_equal; lia]|].
  split; [apply stk_write; [exact ST | lia | cbn [length]; lia]|].
  split; [apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | rewrite FRS; cbn [length]; lia]|].
  apply (u8arr_write asegs m LB bs (len - 3) (Z_to_bv 8 0) DST). rewrite LBS. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CSan.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
(* [comment removed for export] *)
Hypothesis MCMP : memcmp_icontract RT.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
(* [comment removed for export] *)
Hypothesis GO_ctype : GOBJ CTYPE_TAB 256.
Hypothesis GO_bom : GOBJ LIT_BOM 3.

Theorem sanitize_line_proof : sanitize_line_stmt RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary LB len flags fcall bs
         FDO MST -> -> -> -> -> HL HF HC INLB LBAL LBS BUF NUL ART0 MI0 CALL HSTK CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 128 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SAN_STACK in *; lia).
  assert (HLO1 : lo <= usp - 128) by (clear - HSTK; unfold RT_STACK, SAN_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  pose proof (af_live_range RT AF Σ m LB 256 ART0 INLB) as (LB0 & LBLO' & _). assert (LBLO : LB + 256 <= lo) by (clear - LBLO' LOW; lia). clear LBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m LB 256 ART0 INLB ltac:(lia)) as LBHI.
  assert (LBAL8 : LB mod 8 = 0) by (clear - LBAL; Z.div_mod_to_equations; lia).
  set (usp1 := usp + -112).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK, SAN_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 7). lia. }
  (* [comment removed for export] *)
  assert (FIN : forall (mD : mem) (clen : Z) (bsD j0 : list byte) (F' : bvmap 5 word) (fc' : bv 32) (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) c1,
    ART RT Σ mD -> mem_inv asegs mD -> stk asegs mD lo usp1 ->
    rw_cells asegs mD usp1 (CB 8 j0 :: san_saved s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> length j0 = 8%nat ->
    u8arr asegs mD LB bsD -> length bsD = 256%nat -> nth_error bsD (Z.to_nat clen) = Some (Z_to_bv 8 0) -> 1 <= clen <= len ->
    (clen = len /\ bsD = bs \/ clen + 3 <= len) ->
    (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (LB <= bv_unsigned x < LB + 256) -> mD x = m x) -> wmono asegs m mD ->
    ASTA RT Σ PMc (eq (MS (mkR xra (wz usp1) gp (wz TP_A) x5 x6 x7 sp (wz LB) x10 x11 x12 x13 x14 x15 x16 x17 (wz clen) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                           F' (wz J_DISP) fc' None mD (seg_rom asegs))) c1 ->
    realizes asegs c1 T).
  { intros mD clen bsD j0 F' fc' xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 c1 ARTD MID STD FRD LJ0 DSTD LBSD NULD HCL HCASE PD WMD Hc1.
    destruct (af_client_consts RT AF Σ mD ARTD) as (_ & SHCD & _ & _ & UTD).
    pose proof (proj2 (af_acc_live RT AF Σ mD LB 256 ARTD INLB)) as ACLD.
    pose proof (afp_acc_global RT GOBJ AFP Σ mD CTYPE_TAB 256 CTYPE_TAB 256 ARTD GO_ctype ltac:(lia) ltac:(lia)) as ACTD.
    assert (AB : 0 < LB /\ 0x10007fff8000 <= LB /\ LB + 256 <= lo /\ 0x10007fff8000 <= lo /\ lo <= bv_unsigned sp - 128 /\ bv_unsigned sp <= 2 ^ 47 /\ LB mod 16 = 0 /\ 1 <= clen <= 254 /\ length j0 = 8%nat)
      by (fold usp; clear - LB0 LBHI LBLO HLOS HLO1 SPH LBAL HCL HL LJ0; lia).
    assert (ID : INVb ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mD LB lo j0 mD bsD).
    { split; [exact DSTD|]. split; [exact LBSD|]. split; [unfold san_frame; fold usp usp1; exact FRD|]. split; [fold usp usp1; exact STD|]. split; [exact MID|].
      split; [apply munch_refl| apply wmono_refl]. }
    pose proof (san_dispatch ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' mD LB clen lo bsD j0 AB LBAL8 UTD SHCD ACLD ACTD flags mD bsD
                  xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 ID HF NULD eq_refl) as WD.
    fold usp in WD. fold usp1 in WD.
    cl_lift WD Hc1 c2 Hc2. apply Hk. eapply ASTA_conseq; [exact Hc2|]. cbv beta. unfold sanitize_postA.
    intros ms (y5 & y6 & y7 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y28 & y29 & y30 & y31 & len' & bs' & m' & -> & HL1 & HLF & MU & WM & MI' & ST' & LBS' & RC' & NL & NN).
    fold usp in MU, ST'.
    assert (P' : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (LB <= bv_unsigned x < LB + 256) -> m' x = m x).
    { intros x Hx HnL. rewrite <- (PD x Hx HnL). apply MU. unfold san_W. cbn [outside]. split; [clear - HnL; lia|]. split; [| exact I].
      destruct (cl_split RT AF Σ mD usp 128 _ ARTD ltac:(clear - NUM; lia) ltac:(clear; lia) Hx); clear - H; lia. }
    exists (Z_to_bv 64 len'), m'. split; [do 16 eexists; reflexivity|].
    split.
    { split; [| exact (conj MI' ST')].
      apply (wg_seg_ART RT AF Σ mD m' usp 128 [(LB, LB + 256)] ARTD ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU); [| exact WM].
      intros x Hx. right. exists LB, 256. split; [exact INLB|]. cbn [outside] in Hx. clear - Hx. lia. }
    split; [intros x Hx Ho; apply (P' x Hx); cbn [outside] in Ho; clear - Ho; lia|].
    split.
    { apply (cl_env_agree m m' _ _ CLE). intros a Ha. apply P'; [right; left; exact (cl_cell_static _ Ha)|].
      assert (HFP : cl_fp [(LB, LB + 256)]) by cl_fp_lia. pose proof (HFP _ Ha) as X. cbn [outside] in X. clear - X. lia. }
    exists len', bs'. split; [reflexivity|]. split; [clear - HL1 HCL; lia|].
    split; [intros HLB; destruct HCASE as [[-> ->]| H3]; [exact (HLF HLB)| clear - HL1 H3; lia]|].
    split; [exact (wmono_trans asegs _ _ _ WMD WM)|]. exact (conj LBS' (conj RC' (conj NL NN))). }
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (w0_walk ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LB len flags fcall lo ltac:(clear - HLO1; lia) HLOS SPH ST UT SHC LB0 LBLO HL HF HC MI0) as W0.
  fold usp in W0. replace (usp - 112) with usp1 in W0 by (unfold usp1; lia). fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (x5 & x6 & x7 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & j & m1 & MU1 & WM1 & MI1 & ST1 & FR1 & LJ & CASES) & Hc1'). clear Hc1.
  assert (MU1' : munch ([] ++ [(usp - 112, usp)]) m m1) by (cbn [app]; replace (usp - 112) with usp1 by (unfold usp1; lia); exact MU1).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 112 [] ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 112 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx); unfold usp1; clear - H; lia. }
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
  assert (BUF1 : rw_cells asegs m1 LB [CB 256 bs]).
  { apply (rw_cells_agree asegs m m1 _ _ BUF); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P1. apply (acl_live _ _ _ LB 256); [exact INLB | clear - Hx; lia]. }
  pose proof (u8arr_of_rw_cells asegs m1 LB _ bs BUF1) as DST1.
  destruct CASES as [(HNO & (ya & yb & yc & ->)) | (HYES & ->)].
  { (* [comment removed for export] *)
    eapply (FIN m1 len bs j F fc); [exact ART1| exact MI1| exact ST1| exact FR1| exact LJ| exact DST1| exact LBS| exact NUL| clear - HL; lia| left; split; reflexivity
      | intros x Hx _; exact (P1 x Hx)| exact WM1| exact Hc1']. }
  (* [comment removed for export] *)
  pose proof (rw_cells_bytes_at asegs m1 LB _ BUF1) as BB1. cbn [cells_bytes cbytes] in BB1. rewrite app_nil_r in BB1.
  rewrite <- (firstn_skipn 3 bs) in BB1. apply bytes_at_app in BB1. destruct BB1 as [BB1 _].
  assert (LF3 : length (firstn 3 bs) = 3%nat) by (rewrite length_firstn, LBS; reflexivity).
  apply (MCMP Σ PMc (wz SITE_san_mcmp) (wz usp1) gp (wz TP_A) x5 x6 x7 sp (wz LB) (wz LB) (wz LIT_BOM) (wz 3) (wz fcall) y4 y5 y6 y7 (wz len) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
           F fc m1 LB LIT_BOM (firstn 3 bs) bom_lit lo FDO MST eq_refl eq_refl ltac:(rewrite LF3; reflexivity) ltac:(rewrite LF3; reflexivity) ltac:(rewrite LF3; cbn; lia)
           ltac:(clear - LB0 LBLO HLO1 SPH; lia) ltac:(unfold LIT_BOM; clear; lia) BB1 (bom_lit_at m1 MI1)).
  { rewrite LF3. exact (live_checked_src RT AF Σ m1 _ lo LB 256 LB 3 ART1 INLB ltac:(clear; lia) ltac:(clear; lia) LOW). }
  { rewrite LF3. split; [| left; unfold LIT_BOM; clear - HLOS; lia]. intros _. split.
    - exact (afp_acc_global RT GOBJ AFP Σ m1 LIT_BOM 3 LIT_BOM 3 ART1 GO_bom ltac:(clear; lia) ltac:(clear; lia)).
    - right; right; right. unfold LIT_BOM, SEGTOP_A. clear. lia. }
  { exact ART1. } { exact MI1. } { exact CO1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & _) & Hc2'). clear Hc2.
  destruct RS2 as (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2.
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m2 x = m x).
  { intros x Hx. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) ltac:(clear; lia)). exact (P1 x Hx). }
  assert (FR2 : rw_cells asegs m2 usp1 (CB 8 j :: san_saved s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold san_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | clear; lia]. }
  assert (BUF2 : rw_cells asegs m2 LB [CB 256 bs]).
  { apply (rw_cells_agree asegs m m2 _ _ BUF); [| exact (wmono_trans asegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2. apply (acl_live _ _ _ LB 256); [exact INLB | clear - Hx; lia]. }
  pose proof (u8arr_of_rw_cells asegs m2 LB _ bs BUF2) as DST2.
  pose proof (w1_walk gp z0 z1 z2 sp h1 h2 h3 h4 h5 h6 h7 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6 F2 fc2 m2 LB len flags (memcmp_res (firstn 3 bs) bom_lit) usp1
                ltac:(clear - HYES HL; lia) (memcmp_res_range _ _) LB0 ltac:(clear - LBLO HLO1 SPH; fold usp in HLO1; lia) MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & [[HR ->] | [HR ->]] & Hc3'); clear Hc3.
  { (* [comment removed for export] *)
    eapply (FIN m2 len bs j F2 fc2); [exact ART2| exact MI2| exact ST2| exact FR2| exact LJ| exact DST2| exact LBS| exact NUL| clear - HL; lia| left; split; reflexivity
      | intros x Hx _; exact (P2 x Hx)| exact (wmono_trans asegs _ _ _ WM1 WM2)| exact Hc3']. }
  (* [comment removed for export] *)
  pose proof (rw_cells_bytes_at asegs m2 LB _ BUF2) as BB2. cbn [cells_bytes cbytes] in BB2. rewrite app_nil_r in BB2.
  assert (CO2 : call_ok RT Σ m2 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST2 (conj LOW COP))).
  apply (MMV Σ PMc (wz SITE_san_mmv) (wz usp1) gp (wz TP_A) z0 z1 z2 sp (wz LB) (wz LB) (wz (LB + 3)) (wz (len - 3)) h3 h4 h5 h6 h7 (wz (len - 3)) (wz flags) (wz SHB) s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6
           F2 fc2 m2 LB 3 (len - 3) bs lo FDO MST eq_refl eq_refl eq_refl ltac:(clear - LB0 LBLO HLO1 SPH; lia) ltac:(clear; lia) ltac:(clear - HYES; lia)
           ltac:(rewrite LBS; clear - HL; lia) ltac:(rewrite LBS; clear; lia) BB2).
  { exact (live_checked_src RT AF Σ m2 _ lo LB 256 (LB + 3) (len - 3) ART2 INLB ltac:(clear; lia) ltac:(clear - HL; lia) LOW). }
  { rewrite LBS. exact (live_checked_dst RT AF Σ m2 _ LB 256 LB 256 ART2 INLB ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)). }
  { exact ART2. } { exact MI2. } { exact CO2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & MV3) & Hc4'). clear Hc4.
  destruct RS3 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite LBS in PRES3. change (Z.of_nat 256) with 256 in PRES3.
  assert (P3 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (LB <= bv_unsigned x < LB + 256) -> m3 x = m x).
  { intros x Hx HnL. rewrite (PRES3 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) HnL). exact (P2 x Hx). }
  assert (FR3 : rw_cells asegs m3 usp1 (CB 8 j :: san_saved s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m2 m3 _ _ FR2); [| exact WM3]. intros x Hx. cbv beta in Hx. unfold san_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES3; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold usp1 in Hx; clear - Hx LBLO HLO1; lia]. }
  pose proof (af_acc_live RT AF Σ m3 LB 256 ART3 INLB) as (WR3 & ACL3).
  assert (DST3 : u8arr asegs m3 LB (mv_cur (Z.to_nat 3) bs (Z.to_nat (len - 3)))).
  { split; [exact MV3|]. rewrite san_mv_cur_length, LBS by (rewrite LBS; clear - HL HYES; lia). exact WR3. }
  pose proof (w2_walk sp gp w0 w1 w2 sp g1 g2 g3 g4 g5 g6 g7 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m3 LB len flags lo (mv_cur (Z.to_nat 3) bs (Z.to_nat (len - 3))) (CB 8 j :: san_saved s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
                ltac:(clear - HYES HL; lia) LB0 LBHI LBLO ltac:(clear - HLO1; lia) SPH LBAL8 DST3 ltac:(rewrite san_mv_cur_length by (rewrite LBS; clear - HL HYES; lia); exact LBS) ACL3) as W2.
  fold usp in W2. fold usp1 in W2.
  specialize (W2 FR3 ltac:(reflexivity) ST3 MI3).
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & (g1' & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & DST4) & Hc5'). clear Hc5.
  assert (ART4 : ART RT Σ m4).
  { apply (af_frame RT AF Σ m3 m4 usp1 ART3 ltac:(unfold usp1; clear - NUM; lia)); [| exact WM4].
    intros x Hx. apply MU4. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ LB 256); [exact INLB | clear - Hin HL HYES; lia]. }
  eapply (FIN m4 (len - 3) (upd (mv_cur (Z.to_nat 3) bs (Z.to_nat (len - 3))) (Z.to_nat (len - 3)) (Z_to_bv 8 0)) j F3 fc3);
    [exact ART4| exact MI4| exact ST4| exact FR4| exact LJ| exact DST4| rewrite upd_length, san_mv_cur_length by (rewrite LBS; clear - HL HYES; lia); exact LBS
    | apply nth_error_upd_same; rewrite san_mv_cur_length by (rewrite LBS; clear - HL HYES; lia); rewrite LBS; clear - HL HYES; lia| clear - HL HYES; lia| right; clear; lia
    | | exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 WM4)))| exact Hc5'].
  intros x Hx HnL. rewrite <- (P3 x Hx HnL). apply MU4. cbn [outside]. split; [clear - HnL HL HYES; lia| exact I].
Qed.
End CSan.
