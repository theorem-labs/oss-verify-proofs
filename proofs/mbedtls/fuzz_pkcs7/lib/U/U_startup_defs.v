(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StartupTac ArgvEnv Layout.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_startup_defs () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.None"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Defs.envp_w"; "Defs.auxv_w"; "Defs.pn_w"; "Defs.progname_w"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Defs.argv_w"; "Defs.argc_w"; "Defs.aux_base"; "RocqVerifyHarness.AgentSubmission.BB.ZStores.zeros"; "Defs.rnd_w"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Defs.guard_lo"; "Defs.guard_hi"; "Defs.canary_w"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Defs.canary_bytes"].


Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.



Section Defs.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN av.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 av ev.
  (* [comment removed for export] *)
  Definition rnd_bytes : list byte := at_random_bytes (ed_random rdraw).
  Definition guard_lo_bytes : list byte := firstn 4 rnd_bytes.
  Definition guard_hi_bytes : list byte := firstn 4 (skipn 4 rnd_bytes).
  (* [comment removed for export] *)
  Definition guard_lo : word := v_lw (Z_to_bv 64 (bytes_le_to_Z guard_lo_bytes)).
  Definition guard_hi : word := v_lw (Z_to_bv 64 (bytes_le_to_Z guard_hi_bytes)).
  (* [comment removed for export] *)
  Definition canary_bytes : list byte :=
    firstn 1 rnd_bytes ++ [Z_to_bv 8 0] ++ firstn 6 (skipn 2 rnd_bytes).
  Definition canary_w : word := Z_to_bv 64 (bytes_le_to_Z canary_bytes).
  (* [comment removed for export] *)
  Definition secret_bytes : list byte := firstn 8 (skipn 8 rnd_bytes).
  Definition secret_w : word := Z_to_bv 64 (bytes_le_to_Z secret_bytes).

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte := ltac2:(CDefT.buildp (gd_tbl_P_startup_defs ()) "(0.(0.(0.(0.(0.(0.L,(1.&40.)(2.(1.&8.))(3.&40.+5<??8.)(4.#8.$5.))(3.&40.+7=358.)(4.#8.$6.))(3.&40.+7=3;8.)(4.#8.Vhw,))(3.&40.+7=380.)(4.#8.(3.&40.+1000.)))(3.&40.+7=348.)(4.#8.$7.))(3.&40.+7=340.)(4.#8.$8.))")
(* [comment removed for export] *).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte := ltac2:(CDefT.buildp (gd_tbl_P_startup_defs ()) "(0.(0.(0.(0.(0.(0.(0.(0.O1.(3.&40.(9.(:.&40.Vsp0,)+8.))(4.#8.(3.&40.=)))(3.&40.(9.(:.&40.Vsp0,)+10.))(4.#8.(3.&40.=)))(3.&40.(9.(:.&40.Vsp0,)+18.))(4.#8.(3.&40.=)))(3.&40.(9.(:.&40.Vsp0,)+20.))(4.#8.(3.&40.=)))(3.&40.(9.(:.&40.Vsp0,)+28.))(4.#8.(3.&40.+3?238.)))(3.&40.(9.(:.&40.Vsp0,)+30.))(4.#8.$;.))(3.&40.(9.(:.&40.Vsp0,)+38.))(4.#8.$<.))(3.&40.(9.(:.&40.Vsp0,)+40.))(4.#8.(3.&40.+1=24<.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte := ltac2:(CDefT.buildp (gd_tbl_P_startup_defs ()) "(0.(0.(0.(0.(0.(0.(0.(0.(0.(0.O1.$=.(>.#130.))(3.&40.(9.(:.&40.Vsp0,)+158.))(4.#8.(3.&40.+10040.)))(3.&40.(9.(:.&40.Vsp0,)+150.))(4.#8.(3.&40.+38.)))(3.&40.(9.(:.&40.Vsp0,)+148.))(4.#8.(3.&40.+:.)))(3.&40.(9.(:.&40.Vsp0,)+?0.))(4.#8.Vhw,))(3.&40.(9.(:.&40.Vsp0,)+140.))(4.#8.(3.&40.+1000.)))(3.&40.(9.(:.&40.Vsp0,)+118.))(4.#8.Vuid,))(3.&40.(9.(:.&40.Vsp0,)+110.))(4.#8.Vuid,))(3.&40.(9.(:.&40.Vsp0,)+;8.))(4.#8.(3.&40.=)))(3.&40.(9.(:.&40.Vsp0,)+:8.))(4.#8.$?.))")
(* [comment removed for export] *).                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte := ltac2:(CDefT.buildp (gd_tbl_P_startup_defs ()) "(0.(0.(0.(0.(0.(0.(0.(0.(0.(0.O1.(3.&40.+7=0?0.)(4.#8.(3.&40.=)))(3.&40.+7=100.)(4.#8.(3.&40.=)))(3.&40.+7=0?8.)(4.#8.(3.&40.+8.)))(3.&40.+7=368.)(4.#8.(3.&40.+>0.)))(3.&40.+7=370.)(4.#8.(3.&40.+8.)))(3.&40.+5=0=8.)(4.#8.(3.&40.=)))(3.&40.+5=0<0.)(4.#8.(3.&40.+5=0=8.)))(3.&40.+5=000.)(4.#8.(3.&40.+5=000.)))(3.&40.+7=350.)(10.(1.&8.)(3.&8.+1.)(11.(1.&8.))))(3.&40.+5=028.)(4.#4.(3.&40.+2.)))")
(* [comment removed for export] *).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte := ltac2:(CDefT.buildp (gd_tbl_P_startup_defs ()) "(0.(0.(0.(0.(0.(0.O1.(3.&40.+5=020.)(4.#4.O2.))(3.&40.+5=098.)(4.#8.(3.&40.+7=388.)))(3.&40.+5=078.)(4.#8.(3.&40.+5=078.)))(3.&40.+5=008.)(4.#8.(3.&40.+5=000.)))(3.&40.+5=010.)(4.#8.(3.&40.+5=000.)))(3.&40.+5=018.)(4.#8.(3.&40.=)))")
(* [comment removed for export] *).        (* [comment removed for export] *)

  Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
    D_tlsB tid (D_tlsA D).

  (* [comment removed for export] *)
  Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte := ltac2:(CDefT.buildp (gd_tbl_P_startup_defs ()) "(0.(0.(0.(0.(0.(0.(0.O8.(3.&40.(9.(:.&40.Vsp0,)+1:8.))(4.#8.O7.))(3.&40.(9.(:.&40.Vsp0,)+1;0.))(4.#8.O6.))(3.&40.(9.(:.&40.Vsp0,)+1;8.))(4.#8.O5.))(3.&40.(9.(:.&40.Vsp0,)+1<0.))(4.#8.O4.))(3.&40.(9.(:.&40.Vsp0,)+1<8.))(4.#8.O3.))(3.&40.(9.(:.&40.Vsp0,)+1=0.))(4.#8.O2.))(3.&40.(9.(:.&40.Vsp0,)+1=8.))(4.#8.O1.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition D_ssp (D : word -> option byte) : word -> option byte := ltac2:(CDefT.buildp (gd_tbl_P_startup_defs ()) "(0.(0.(0.(0.O1.(3.&40.+7=330.)(4.#4.$12.))(3.&40.+7=334.)(4.#4.$13.))(3.&40.+7=331.)(10.(1.&8.)(3.&8.=)(11.(1.&8.))))(3.&40.+5=0;8.)(4.#8.$14.))")
(* [comment removed for export] *).         (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma length_rnd_bytes : length rnd_bytes = 16%nat.
  Proof. unfold rnd_bytes. apply length_at_random_bytes. Qed.
  #[using="Type"] Lemma length_guard_lo_bytes : length guard_lo_bytes = 4%nat.
  Proof. unfold guard_lo_bytes. rewrite firstn_length, length_rnd_bytes. reflexivity. Qed.
  #[using="Type"] Lemma length_guard_hi_bytes : length guard_hi_bytes = 4%nat.
  Proof. unfold guard_hi_bytes. rewrite firstn_length, skipn_length, length_rnd_bytes. reflexivity. Qed.
  #[using="Type"] Lemma length_canary_bytes : length canary_bytes = 8%nat.
  Proof. unfold canary_bytes. rewrite !app_length, !firstn_length, skipn_length, length_rnd_bytes. reflexivity. Qed.
  #[using="Type"] Lemma length_secret_bytes : length secret_bytes = 8%nat.
  Proof. unfold secret_bytes. rewrite firstn_length, skipn_length, length_rnd_bytes. reflexivity. Qed.

  #[using="Type"] Lemma bytes_le_to_Z_lt : forall bs k, length bs = k -> (0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat k))%Z.
  Proof.
    intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bytes_val : forall bs, (length bs <= 8)%nat -> bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
  Proof.
    intros bs Hl. pose proof (bytes_le_to_Z_lt bs (length bs) eq_refl) as B.
    assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia).
    symmetry. apply u_Z2bv; lia.
  Qed.
  #[using="Type"] Lemma guard_lo_val : bytes_le_to_Z guard_lo_bytes = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z guard_lo_bytes)).
  Proof. apply bytes_val. rewrite length_guard_lo_bytes. lia. Qed.
  #[using="Type"] Lemma guard_hi_val : bytes_le_to_Z guard_hi_bytes = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z guard_hi_bytes)).
  Proof. apply bytes_val. rewrite length_guard_hi_bytes. lia. Qed.
  #[using="Type"] Lemma canary_val : bytes_le_to_Z canary_bytes = bv_unsigned canary_w.
  Proof. unfold canary_w. apply bytes_val. rewrite length_canary_bytes. lia. Qed.
  #[using="Type"] Lemma secret_val : bytes_le_to_Z secret_bytes = bv_unsigned secret_w.
  Proof. unfold secret_w. apply bytes_val. rewrite length_secret_bytes. lia. Qed.


  (* [comment removed for export] *)
  #[using="Type"] Lemma lor_shl8_low' : forall b r, (0 <= b < 256)%Z -> (0 <= r)%Z -> Z_to_bv 8 (Z.lor b (Z.shiftl r 8)) = Z_to_bv 8 b.
  Proof.
    intros b r Hb Hr. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8)%Z. cbv beta.
    change (bv_wrap 8 b) with (b mod 2^8)%Z.
    apply Z.bits_inj'. intros i Hi.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
      rewrite (Z.testbit_neg_r r (i - 8)) by lia. apply orb_false_r.
    - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma lor_shl8_high' : forall b r, (0 <= b < 256)%Z -> (0 <= r)%Z -> Z.shiftr (Z.lor b (Z.shiftl r 8)) 8 = r.
  Proof.
    intros b r Hb Hr. rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma Z_to_le_bytes_to_Z' : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
  Proof.
    induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
    pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. pose proof (bytes_le_to_Z_nonneg bs).
    f_equal.
    - rewrite lor_shl8_low' by (cbn in Hb; lia). apply Z_to_bv_bv_unsigned.
    - rewrite lor_shl8_high' by (cbn in Hb; lia). exact IH.
  Qed.
  #[using="Type"] Lemma bv_wrap_swrap' : forall n z, bv_wrap n (bv_swrap n z) = bv_wrap n z.
  Proof.
    intros n z. unfold bv_swrap. unfold bv_wrap.
    pose proof (bv_modulus_pos n) as P.
    set (M := bv_modulus n) in *. set (h := bv_half_modulus n).
    assert (E : ((z + h) mod M = (z + h) - M * ((z + h) / M))%Z) by (pose proof (Z.div_mod (z+h) M ltac:(lia)); lia).
    rewrite E. replace (z + h - M * ((z + h) / M) - h)%Z with (z + (- ((z + h) / M)) * M)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma lw_sw_bytes : forall bs, length bs = 4%nat ->
    word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))) = bs.
  Proof.
    intros bs Hl. unfold word_to_le_bytes, v_lw.
    rewrite Z_to_bv_unsigned. rewrite (Z_to_le_bytes_wrap 4 64) by (cbn; lia).
    rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_swrap 32 _)) by (cbn; lia).
    rewrite bv_wrap_swrap'. rewrite (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
    rewrite <- (bytes_val bs) by (rewrite Hl; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z'.
  Qed.
  #[using="Type"] Lemma guard_lo_store : word_to_le_bytes 4 guard_lo = guard_lo_bytes.
  Proof. apply lw_sw_bytes. apply length_guard_lo_bytes. Qed.
  #[using="Type"] Lemma guard_hi_store : word_to_le_bytes 4 guard_hi = guard_hi_bytes.
  Proof. apply lw_sw_bytes. apply length_guard_hi_bytes. Qed.
  #[using="Type"] Lemma canary_store : word_to_le_bytes 8 canary_w = canary_bytes.
  Proof.
    unfold word_to_le_bytes. rewrite <- canary_val. rewrite <- length_canary_bytes. apply Z_to_le_bytes_to_Z'.
  Qed.
  #[using="Type"] Lemma secret_store : word_to_le_bytes 8 secret_w = secret_bytes.
  Proof.
    unfold word_to_le_bytes. rewrite <- secret_val. rewrite <- length_secret_bytes. apply Z_to_le_bytes_to_Z'.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma guard_read : ltac2:(CDefT.buildp (gd_tbl_P_startup_defs ()) "Psegs,(15.$16.)PDD,P,(1.&40.)(17.(1.&8.))(18.(17.(15.(1.&8.)))(19.R2.(0.(0.(0.R1.(3.&40.+7=330.)(4.#4.$12.))(3.&40.+7=334.)(4.#4.$13.))(3.&40.+7=331.)(10.(1.&8.)(3.&8.=)(11.(1.&8.))))(3.&40.+7=330.)#8.)(1:.(15.(1.&8.))$1;.))")
(* [comment removed for export] *).
  Proof.
    intros segs DD. rewrite guard_lo_store, guard_hi_store.
    unfold canary_bytes, guard_lo_bytes, guard_hi_bytes, rnd_bytes, at_random_bytes.
    cbn [firstn skipn app].
    set (b0 := bv_extract 0 8 _). set (b1 := bv_extract 8 8 _). set (b2 := bv_extract 16 8 _). set (b3 := bv_extract 24 8 _).
    set (b4 := bv_extract 32 8 _). set (b5 := bv_extract 40 8 _). set (b6 := bv_extract 48 8 _). set (b7 := bv_extract 56 8 _).
    clearbody b0 b1 b2 b3 b4 b5 b6 b7. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x4cf20) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
