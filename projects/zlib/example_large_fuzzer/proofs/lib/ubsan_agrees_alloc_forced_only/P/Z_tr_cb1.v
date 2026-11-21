(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition cbR (L : dlay) (LT DT sx : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz 65535) (wz Z_LENGTH_CODE) (wz 4) s0 s1 (wz (dl_As L)) (wz LT) (wz DT) (wz (dl_As L + 5888)) (wz sx)
      (wz 16) (wz (-20)) (wz 257) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Definition cb_site_post (EXIT : Z) (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 t4 t5 t6 wbb m',
    ms' = MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV) t4 t5 t6) F (wz EXIT) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

(* [comment removed for export] *)
Lemma cb_S1 : forall (L : dlay) (s : deflate_state) (lfc ldl : arr) (LT DT sx lc : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> 0 <= lc < 286 -> 0 < LT -> LT + 4 * 286 < 2^63 ->
  0 <= arr_get lfc lc < 65536 -> 0 <= arr_get ldl lc <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - arr_get ldl lc < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site_post 0x1c60c L s LT DT sx (sbF_PB PB PD BB BV (arr_get lfc lc) (arr_get ldl lc)) (sbF_PD PD BV (arr_get ldl lc))
                          (sbF_BB BB BV (arr_get lfc lc) (arr_get ldl lc)) (sbF_BV BV (arr_get ldl lc)) ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 (wz lc)) F (wz 0x1c6f0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RDL Rlc RLT1 RLT2 RV Rl RBV RPD ROOM. unfold cbR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI lc Rlc) as [RDc RDl].
  do 2 zstep. shl_norm.
  zs. rewrite (zx16_small (arr_get lfc lc)) by lia. zs. rewrite (zx16_small (arr_get ldl lc)) by lia.
  zs. zs. zs. zs. zs.
  set (V := arr_get lfc lc) in *. set (l := arr_get ldl lc) in *. clearbody V l.
  sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
  zs. zstep. br_cases K.
  - (* [comment removed for export] *)
    zs2. zs2.
    apply evt_done. unfold cb_site_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  - (* [comment removed for export] *)
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_site_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

(* [comment removed for export] *)
Definition cb_site2_post (X : Z -> Prop) (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (vs0 vt3 vt6 : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s1 s2 s3 s4 s5 w wbb pcx m',
    ms' = MS (cbR L LT DT sx ra sp gp tp (wz vs0) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz vt3) w (wz BV) (wz vt6)) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16 /\ bv_unsigned w mod 2^16 = BB mod 2^16 /\ X pcx.

Lemma unsigned_wz_neg : forall z, - 2^63 <= z < 0 -> bv_unsigned (wz z) = z + 2^64.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma cb_range_test : forall code, 0 <= code < 29 -> bv_ltu (wz (code + -28)) (wz (-20)) = negb ((8 <=? code) && (code <=? 27)).
Proof.
  intros code H. unfold bv_ltu. rewrite (unsigned_wz_neg (-20)) by lia.
  destruct (Z.eq_dec code 28) as [->|NE].
  - change (28 + -28) with 0. rewrite unsigned_lit by lia. reflexivity.
  - rewrite unsigned_wz_neg by lia.
    destruct (Z.leb_spec 8 code), (Z.leb_spec code 27); cbn [andb negb]; [apply Z.ltb_ge| | apply Z.ltb_lt| apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Ltac cb_fin2 MU WM GA GD Gpend LOc LOr side EXT :=
  apply evt_done; unfold cb_site2_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV;
  rewrite ?(proj2 (Z.ltb_ge _ _)), ?(proj2 (Z.ltb_lt _ _)) by lia; do 9 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LOc|]; split; [LOr|]; side; (split; [reflexivity| EXT]).

(* [comment removed for export] *)
Lemma cb_S2 : forall (L : dlay) (s : deflate_state) (lfc ldl : arr) (LT DT sx lc dist code V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  code = arr_get length_code_a lc -> V = arr_get lfc (code + 257) -> l = arr_get ldl (code + 257) ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> 0 <= lc < 256 -> 0 < LT -> LT + 4 * 286 < 2^63 ->
  0 <= V < 65536 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site2_post (fun pcx => (pcx = 0x1c77c /\ 8 <= code <= 27) \/ (pcx = 0x1c818 /\ ~ (8 <= code <= 27)))
                           L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (code * 4) dist lc
                           ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz dist) t4 t5 (wz lc)) F (wz 0x1c660) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Ecode EV El EMH HBB MI LAY RDL Rlc RLT1 RLT2 RV Rl RBV RPD ROOM. unfold cbR.
  pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI (code + 257) ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  pose proof (u8ro_read psegs m Z_LENGTH_CODE (av8 length_code_a 256) lc _ (wa (Z_LENGTH_CODE + lc)) (rod_length_code m MI)
                (av8_nth length_code_a 256 lc ltac:(lia)) ltac:(lia) eq_refl) as RDlc. rewrite <- Ecode in RDlc.
  unfold Z_LENGTH_CODE in *.
  zs2. zsb. rewrite (bv8_small code) by lia.
  zs2. shl_norm. zs2.
  zs2. rewrite (zx16_small V) by lia. zs2. rewrite (zx16_small l) by lia.
  clear Ecode EV El.
  zs2. zs2. zs2. zs2. zs2.
  sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
  zs2. zstep. br_cases K.
  - (* [comment removed for export] *)
    zs2. zs2. zs2. zstep. rewrite cb_range_test by lia.
    destruct ((8 <=? code) && (code <=? 27)) eqn:EX; cbn [negb].
    + cb_fin2 MU WM GA GD Gpend ltac:(exact LO) ltac:(exact LO) ltac:(left) ltac:(rewrite andb_true_iff, !Z.leb_le in EX; lia).
    + cb_fin2 MU WM GA GD Gpend ltac:(exact LO) ltac:(exact LO) ltac:(right) ltac:(rewrite andb_false_iff, !Z.leb_gt in EX; lia).
  - (* [comment removed for export] *)
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. zstep. reg_as (l + BV + -16) (BV + l - 16). rewrite cb_range_test by lia.
    destruct ((8 <=? code) && (code <=? 27)) eqn:EX; cbn [negb].
    + cb_fin2 MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(rewrite andb_true_iff, !Z.leb_le in EX; lia).
    + zstep.
      cb_fin2 MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(rewrite andb_false_iff, !Z.leb_gt in EX; lia).
Qed.
