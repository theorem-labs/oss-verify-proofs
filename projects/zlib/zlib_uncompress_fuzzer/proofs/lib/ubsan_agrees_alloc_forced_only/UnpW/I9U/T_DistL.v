(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg LibMaskBits.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import S_DistL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U Require Import TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_DLOOP1_T : Z := 94480.  (* [comment removed for export] *)
Definition L_DL1X_T : Z := 94608.    (* [comment removed for export] *)
Definition L_DLOOP2_T : Z := 94720.  (* [comment removed for export] *)
Definition L_DL2X_T : Z := 94876.    (* [comment removed for export] *)
Definition L_DXLOOP_T : Z := 95036.  (* [comment removed for export] *)
Definition L_DXE8_T : Z := 95120.    (* [comment removed for export] *)
Definition L_LVX_L1_T : Z := 95936.  (* [comment removed for export] *)
Definition L_LVX_LL1_T : Z := 96024. (* [comment removed for export] *)
Definition L_LVX_L2_T : Z := 96132.  (* [comment removed for export] *)
Definition L_LVX_XD_T : Z := 96160.  (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cellv (e : Z) : Z := code_op e + 256 * code_bits e + 65536 * code_val e.

Lemma lo16_eq : forall e, e mod 65536 = code_op e + 256 * code_bits e.
Proof.
  intros e. rewrite code_op_eq, code_bits_eq, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  change 65536 with (256 * 256). rewrite (Z.rem_mul_r e 256 256) by lia. lia.
Qed.
Lemma cellv_range : forall e, 0 <= cellv e < 4294967296.
Proof.
  intros e. unfold cellv. pose proof (code_op_range e). pose proof (code_bits_range e). pose proof (code_val_range e). lia.
Qed.

(* [comment removed for export] *)
Lemma land_low_shiftl : forall a m s, 0 <= s -> 0 <= a < 2 ^ s -> Z.land a (Z.shiftl m s) = 0.
Proof.
  intros a m s Hs Ha. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i s) as [Hl|Hg].
  - rewrite Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite (testbit_high s a i) by lia. reflexivity.
Qed.
Lemma lor_low_shiftl : forall a m s, 0 <= s -> 0 <= a < 2 ^ s -> Z.lor (Z.shiftl m s) a = a + m * 2 ^ s.
Proof.
  intros a m s Hs Ha.
  assert (D : Z.land a (m * 2 ^ s) = 0) by (rewrite <- Z.shiftl_mul_pow2 by lia; apply land_low_shiftl; lia).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm.
  rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D.
Qed.
(* [comment removed for export] *)
Lemma land_add_high : forall a m s c, 0 <= s -> 0 <= a < 2 ^ s -> 0 <= c < 2 ^ s ->
  Z.land (a + m * 2 ^ s) c = Z.land a c.
Proof.
  intros a m s c Hs Ha Hc. rewrite <- (lor_low_shiftl a m s Hs Ha).
  rewrite Z.land_lor_distr_l. rewrite (Z.land_comm (Z.shiftl m s) c), (land_low_shiftl c m s Hs Hc).
  apply Z.lor_0_l.
Qed.
Lemma land_ones_id : forall x n, 0 <= n -> 0 <= x < 2 ^ n -> Z.land x (2 ^ n - 1) = x.
Proof. intros x n Hn Hx. replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia). apply land_ones_low; assumption. Qed.
Lemma land_zero_high : forall x c n, 0 <= n -> 0 <= x < 2 ^ n -> c mod 2 ^ n = 0 -> Z.land x c = 0.
Proof.
  intros x c n Hn Hx Hc. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i n) as [Hl|Hg].
  - replace (Z.testbit c i) with (Z.testbit (c mod 2 ^ n) i) by (rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_low by lia; apply Bool.andb_true_r).
    rewrite Hc, Z.bits_0. apply Bool.andb_false_r.
  - rewrite (testbit_high n x i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell_or : forall e, Z.lor (Z.shiftl (code_val e) 16) (code_op e + 256 * code_bits e) = cellv e.
Proof.
  intros e. pose proof (code_op_range e). pose proof (code_bits_range e).
  unfold cellv. rewrite lor_low_shiftl by (try lia; change (2 ^ 16) with 65536; lia). change (2 ^ 16) with 65536. lia.
Qed.
Lemma cell_shr8 : forall e, Z.shiftr (cellv e mod 18446744073709551616) 8 = code_bits e + 256 * code_val e.
Proof.
  intros e. pose proof (cellv_range e). pose proof (code_op_range e). rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. unfold cellv.
  replace (code_op e + 256 * code_bits e + 65536 * code_val e) with (code_op e + (code_bits e + 256 * code_val e) * 256) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma cell_shr16 : forall e, Z.shiftr (cellv e mod 18446744073709551616) 16 = code_val e.
Proof.
  intros e. pose proof (cellv_range e). pose proof (code_op_range e). pose proof (code_bits_range e). rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. unfold cellv.
  replace (code_op e + 256 * code_bits e + 65536 * code_val e) with ((code_op e + 256 * code_bits e) + code_val e * 65536) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma cell_and255 : forall e, Z.land (cellv e) 255 = code_op e.
Proof.
  intros e. pose proof (code_op_range e). pose proof (code_bits_range e). pose proof (code_val_range e). unfold cellv.
  replace (code_op e + 256 * code_bits e + 65536 * code_val e) with (code_op e + (code_bits e + 256 * code_val e) * 2 ^ 8) by (change (2 ^ 8) with 256; lia).
  rewrite land_add_high by (try lia; change (2 ^ 8) with 256; lia).
  change 255 with (2 ^ 8 - 1). apply land_ones_id; [lia | change (2 ^ 8) with 256; lia].
Qed.
Lemma cell_and15 : forall e, Z.land (cellv e) 15 = Z.land (code_op e) 15.
Proof.
  intros e. pose proof (code_op_range e). pose proof (code_bits_range e). pose proof (code_val_range e). unfold cellv.
  replace (code_op e + 256 * code_bits e + 65536 * code_val e) with (code_op e + (code_bits e + 256 * code_val e) * 2 ^ 8) by (change (2 ^ 8) with 256; lia).
  apply land_add_high; [lia | change (2 ^ 8) with 256; lia | change (2 ^ 8) with 256; lia].
Qed.
Lemma bits_and255 : forall e, Z.land (code_bits e + 256 * code_val e) 255 = code_bits e.
Proof.
  intros e. pose proof (code_bits_range e). pose proof (code_val_range e).
  replace (code_bits e + 256 * code_val e) with (code_bits e + code_val e * 2 ^ 8) by (change (2 ^ 8) with 256; lia).
  rewrite land_add_high by (try lia; change (2 ^ 8) with 256; lia).
  change 255 with (2 ^ 8 - 1). apply land_ones_id; [lia | change (2 ^ 8) with 256; lia].
Qed.
Lemma bits_and31 : forall e, code_bits e < 32 -> Z.land (code_bits e + 256 * code_val e) 31 = code_bits e.
Proof.
  intros e Hb. pose proof (code_bits_range e). pose proof (code_val_range e).
  replace (code_bits e + 256 * code_val e) with (code_bits e + code_val e * 2 ^ 8) by (change (2 ^ 8) with 256; lia).
  rewrite land_add_high by (try lia; change (2 ^ 8) with 256; lia).
  change 31 with (2 ^ 5 - 1). apply land_ones_id; [lia | change (2 ^ 5) with 32; lia].
Qed.
Lemma bits_and192 : forall e, code_bits e < 64 -> Z.land (code_bits e + 256 * code_val e) 192 = 0.
Proof.
  intros e Hb. pose proof (code_bits_range e). pose proof (code_val_range e).
  replace (code_bits e + 256 * code_val e) with (code_bits e + code_val e * 2 ^ 8) by (change (2 ^ 8) with 256; lia).
  rewrite land_add_high by (try lia; change (2 ^ 8) with 256; lia).
  apply (land_zero_high _ _ 6); [lia | change (2 ^ 6) with 64; lia | reflexivity].
Qed.
Lemma cell_and_e000 : forall e, code_bits e < 32 -> Z.land (cellv e) 57344 = 0.
Proof.
  intros e Hb. pose proof (code_op_range e). pose proof (code_bits_range e). pose proof (code_val_range e). unfold cellv.
  replace (code_op e + 256 * code_bits e + 65536 * code_val e) with ((code_op e + 256 * code_bits e) + code_val e * 2 ^ 16) by (change (2 ^ 16) with 65536; lia).
  rewrite land_add_high by (try lia; change (2 ^ 16) with 65536; lia).
  apply (land_zero_high _ _ 13); [lia | change (2 ^ 13) with 8192; lia | reflexivity].
Qed.
(* [comment removed for export] *)
Lemma shamt_cell : forall e, code_bits e < 64 -> (code_bits e + 256 * code_val e) mod 64 = code_bits e.
Proof.
  intros e Hb. pose proof (code_bits_range e). pose proof (code_val_range e).
  replace (code_bits e + 256 * code_val e) with (code_bits e + (4 * code_val e) * 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* [comment removed for export] *)
Lemma zext32_shift29 : forall x, 0 <= x < 536870912 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 29 = 8 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (8 * 2 ^ 29). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma shl_2 : forall x, Z.shiftl x 2 = 4 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.
Lemma shl_3 : forall x, Z.shiftl x 3 = 8 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.
Lemma land_mask_l' : forall x k, 0 <= k -> 0 <= Z.land (2 ^ k + -1) x < 2 ^ k.
Proof. intros x k Hk. replace (2 ^ k + -1) with (2 ^ k - 1) by lia. apply land_mask_l. exact Hk. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_arr4_lo16 {RCa1 : RunCtx}  : forall M base n f i, mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M base n f -> 0 <= i < n ->
  mem_u16 (run_segments R_segs rc_inp rc_sp rc_mb) M (base + 4 * i) ((f i) mod 65536).
Proof.
  intros M base n f i Ha Hi. pose proof (mem_arr_get (run_segments R_segs rc_inp rc_sp rc_mb) 4 M base n f i Ha Hi) as G.
  change (Z.to_nat 4) with (2 + 2)%nat in G. rewrite Z_to_le_bytes_add in G.
  pose proof (mem_is_app_l (run_segments R_segs rc_inp rc_sp rc_mb) M _ _ _ G) as G0.
  unfold mem_u16. rewrite Z_to_le_bytes_2_mod. exact G0.
Qed.
Lemma zu_lhu_arr4_lo {RCa1 : RunCtx}  : forall pc Rb l M MD T w rd rs (imm : bv 12) base n f i,
  fetch_word (run_segments R_segs rc_inp rc_sp rc_mb) (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M base n f -> zrd_l Rb l rs + bv_signed imm = base + 4 * i -> 0 <= i < n ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (pc + 4) (zupd Rb (wb rd (code_op (f i) + 256 * code_bits (f i)) l)) M MD) T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  intros until T. intros w rd rs imm base n f i F E D Hh Ha Heq Hi Hk.
  pose proof (mem_arr4_lo16 M base n f i Ha Hi) as H2.
  eapply zu_lhu; [exact F | exact E | exact D | exact Hh | |].
  - rewrite Heq. exact (mem_u16_rdn _ _ _ _ H2).
  - pose proof (bytes_le_cell 2 ((f i) mod 65536) ltac:(lia)) as B. change (Z.to_nat 2) with 2%nat in B.
    rewrite B. unfold cell_mod. change (2 ^ (8 * 2)) with 65536.
    rewrite Z.mod_mod by lia. rewrite lo16_eq. exact Hk.
Qed.

Ltac tld4_lo Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lhu_arr4_lo _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_val Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lhu_arr4_val (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
(* [comment removed for export] *)
Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.

(* [comment removed for export] *)
Ltac tcell Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ _ _ ?f =>
    tld4_val Ha i; tld4_lo Ha i; zstep Rfd; zstep Rfd; zsetreg (cellv (f i)) ltac:(symmetry; apply cell_or)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_D1T : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 14; 19; 20; 22; 23; 24; 25; 26; 27; 28; 30; 32]%positive.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_D2T : list positive := [2; 3; 4; 5; 6; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 20; 26; 28; 29; 30; 32]%positive.   (* a worker 1.4 UBSan: d_loop2 writes s7 (24); 1.3.1's kept s8 stays key 25 here *)
(* [comment removed for export] *)
Definition KS_XDT : list positive := [2; 3; 4; 5; 8; 9; 10; 11; 13; 15; 17; 19; 20; 22; 23; 24; 26; 27; 28; 29; 30; 31; 32]%positive.   (* [comment removed for export] *)

Ltac keptc_closeT := cbv [keptc KS_D1T KS_D2T KS_XDT]; split_conj; try exact I; zreg.
Ltac keptc_chainT HK := cbv [keptc KS_D1T KS_D2T KS_XDT] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_loop1_t {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n da nd db dm c0 b0 ci B H : Z) (fin rdD : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA1 = da -> zget_l Rb l kT4 = dm -> zget_l Rb l kA3 = 1 -> zget_l Rb l kT2 = Z.land dm H ->
  zget_l Rb l kT0 = q + ci -> zget_l Rb l kT1 = q + ci -> zget_l Rb l kA5 = B -> zget_l Rb l kA4 = B ->
  zget_l Rb l kA6 = n - ci -> zget_l Rb l kA7 = 8 * (n - ci) -> zget_l Rb l kA2 = n - ci -> zget_l Rb l kS4 = H ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B <= 40 -> (ci = c0 \/ B <= 22) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  dm = 2 ^ db + -1 -> 1 <= db -> db <= 15 -> 2 ^ db <= nd -> tab_ok DISTS rdD db nd = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < da -> da + 4 * nd <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M da nd rdD ->
  (* [comment removed for export] *)
  (forall R' (H' : Z),
     zget R' kS4 = H' -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_D1T ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L1_T (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' (ci' B' H' : Z),
     zget R' kT0 = q + ci' -> zget R' kT1 = q + ci' -> zget R' kA5 = B' -> zget R' kA4 = B' ->
     zget R' kA6 = n - ci' -> zget R' kA7 = 8 * (n - ci') -> zget R' kA2 = n - ci' -> zget R' kS4 = H' ->
     zget R' kT5 = cellv (rdD (Z.land dm H')) -> zget R' kT2 = code_bits (rdD (Z.land dm H')) + 256 * code_val (rdD (Z.land dm H')) ->
     zget R' kT3 = code_bits (rdD (Z.land dm H')) ->
     ci <= ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> B' <= 40 -> code_bits (rdD (Z.land dm H')) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_D1T ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DL1X_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DLOOP1_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n da nd db dm c0 b0 ci B H fin rdD Hh La1 Lt4 La3 Lt2 Lt0 Lt1 La5 La4 La6 La7 La2 Ls3
    HN Hc0 Hc1 Hc2 Hb0 HB HB40 HB22 HH1 HH2 HBc Hdm Hdb1 Hdb2 Hnd TOK Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_DLOOP1_T, L_DL1X_T, L_LVX_L1_T in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 db ltac:(lia)) as HPdb.
  pose proof (land_mask_l' H db ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  set (i := Z.land dm H) in *.
  pose proof (tab_root_entry DISTS rdD db nd i TOK Ri0) as (Hbits0 & _ & _ & _).
  pose proof (code_op_range (rdD i)) as Rop. pose proof (code_val_range (rdD i)) as Rval. pose proof (cellv_range (rdD i)) as Rcell.
  assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * i) ltac:(symmetry; apply shl_2).
  zstep Rfd.                          (* [comment removed for export] *)
  tcell Htab i.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (code_bits (rdD i) + 256 * code_val (rdD i)) ltac:(symmetry; apply cell_shr8).
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (code_bits (rdD i)) ltac:(symmetry; apply bits_and255).
  destruct (Z_lt_dec B (code_bits (rdD i))) as [Hneed | Hok].
  2: { zbr Rfd true.                  (* [comment removed for export] *)
    subst i.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx ci B H) end; try zreg; try lia.
    keptc_closeT. }
  zbr Rfd false.
  assert (HB14 : B <= 14) by lia.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b0 + 8 * (n - c0)) with B by lia. lia.
    - keptc_closeT. }
  zbr Rfd false.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.                   (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (land_mask_l' H' db ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * Z.land dm H') ltac:(symmetry; apply shl_2).
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd. zbool.                   (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd. zlit.                    (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (IH Rx lx Mx MD T q n da nd db dm c0 b0 (ci + 1) (B + 8) H' fin rdD Hh) end;
    try zreg; try lia; try eassumption.
  (* [comment removed for export] *)
  intros R' ci' B' H'' G6 G7 G16 G15 G17 G18 G13 G20 G31 G8 G29 X0 X1 X2 X3 X4 X5 X6 X7 HK.
  eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chainT HK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_loop2_t {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n da nd db lo v m2 c1 b1 ci B H : Z) (fin rdD : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA1 = da -> zget_l Rb l kT6 = m2 -> zget_l Rb l kT3 = db -> zget_l Rb l kT4 = v -> zget_l Rb l kA3 = 1 ->
  zget_l Rb l kT5 = v + Z.land H m2 / 2 ^ db ->
  zget_l Rb l kS10 = q + ci -> zget_l Rb l kT1 = q + ci -> zget_l Rb l kS5 = B -> zget_l Rb l kS2 = db - 8 * (ci - c1) ->
  zget_l Rb l kA2 = n - ci -> zget_l Rb l kS4 = H ->
  n - ci < Z.of_nat N -> 0 <= c1 -> c1 <= ci -> ci <= n -> 0 <= b1 -> B = b1 + 8 * (ci - c1) ->
  B <= 40 -> (ci = c1 \/ B <= 37) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  m2 = 2 ^ (db + lo) - 1 -> 1 <= db -> db <= 15 -> 1 <= lo -> lo <= 15 - db -> 0 <= v -> v + 2 ^ lo <= nd -> nd <= 65536 ->
  (forall j, 0 <= j < 2 ^ lo -> is_linkop (code_op (rdD (v + j))) = false /\ term_ok DISTS (15 - db) (rdD (v + j)) = true) ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < da -> da + 4 * nd <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M da nd rdD ->
  (* [comment removed for export] *)
  (forall R' (H' : Z),
     zget R' kS4 = H' -> 0 <= H' -> H' < 2 ^ (b1 + 8 * (n - c1)) -> b1 + 8 * (n - c1) <= 29 -> b1 + 8 * (n - c1) <= 8 * n ->
     keptc Rb l R' KS_D2T ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L2_T (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' (ci' B' H' : Z),
     zget R' kS10 = q + ci' -> zget R' kT1 = q + ci' -> zget R' kS5 = B' -> zget R' kS2 = db - 8 * (ci' - c1) ->
     zget R' kA2 = n - ci' -> zget R' kS4 = H' ->
     zget R' kT5 = cellv (rdD (v + Z.land H' m2 / 2 ^ db)) ->
     zget R' kS7 = code_bits (rdD (v + Z.land H' m2 / 2 ^ db)) + 256 * code_val (rdD (v + Z.land H' m2 / 2 ^ db)) ->   (* [comment removed for export] *)
     zget R' kS6 = code_bits (rdD (v + Z.land H' m2 / 2 ^ db)) ->
     zget R' kS8 = code_bits (rdD (v + Z.land H' m2 / 2 ^ db)) + db ->   (* a worker 1.4 UBSan: the dist loop keeps s7 here (region map: s7 -> s7, s8 -> s7) *)
     ci <= ci' -> ci' <= n -> B' = b1 + 8 * (ci' - c1) -> B' <= 40 -> db + code_bits (rdD (v + Z.land H' m2 / 2 ^ db)) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_D2T ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DL2X_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DLOOP2_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n da nd db lo v m2 c1 b1 ci B H fin rdD Hh La1 Lt6 Lt3 Lt4 La3 Lt5
    Ls9 Lt1 Ls4 Ls1 La2 Ls3 HN Hc0 Hc1 Hc2 Hb0 HB HB40 HB37 HH1 HH2 HBc Hm2 Hdb1 Hdb2 Hlo1 Hlo2 Hv1 Hv2 Hnd SUB
    Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_DLOOP2_T, L_DL2X_T, L_LVX_L2_T in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 db ltac:(lia)) as HPdb. pose proof (pow2_15 lo ltac:(lia)) as HPlo.
  assert (HPm : 1 <= 2 ^ (db + lo) <= 32768) by (apply pow2_15; lia).
  assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ db < 2 ^ lo).
  { intros Hx. pose proof (land_mask_r Hx (db + lo) ltac:(lia)) as A. rewrite <- Hm2 in A.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
  pose proof (JR H) as Rj0.
  set (j0 := Z.land H m2 / 2 ^ db) in *.
  destruct (SUB _ Rj0) as [_ TM0]. apply term_ok_DISTS in TM0 as [Hbits0 _].
  pose proof (code_op_range (rdD (v + j0))) as Rop. pose proof (code_val_range (rdD (v + j0))) as Rval. pose proof (cellv_range (rdD (v + j0))) as Rcell.
  assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * (v + j0)) ltac:(symmetry; apply shl_2).
  zstep Rfd.                          (* [comment removed for export] *)
  tcell Htab (v + j0).                (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (code_bits (rdD (v + j0)) + 256 * code_val (rdD (v + j0))) ltac:(symmetry; apply cell_shr8).
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (code_bits (rdD (v + j0))) ltac:(symmetry; apply bits_and255).
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z_lt_dec B (code_bits (rdD (v + j0)) + db)) as [Hneed | Hok].
  2: { zbr Rfd true.                  (* [comment removed for export] *)
    subst j0.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx ci B H) end; try zreg; try lia.
    keptc_closeT. }
  zbr Rfd false.
  assert (HB29 : B <= 29) by lia.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b1 + 8 * (n - c1)) with B by lia. lia.
    - keptc_closeT. }
  zbr Rfd false.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.                   (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (land_mask_r H' (db + lo) ltac:(lia)) as Rm. rewrite <- Hm2 in Rm.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (Z.land H' m2 / 2 ^ db) ltac:(symmetry; apply srlw_small; lia).
  pose proof (JR H') as Rj1.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (v + Z.land H' m2 / 2 ^ db) ltac:(lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * (v + Z.land H' m2 / 2 ^ db)) ltac:(symmetry; apply zext32_shift30; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd. zext32.                  (* [comment removed for export] *)
  zstep Rfd. zbool.                   (* [comment removed for export] *)
  zstep Rfd. zlit.                    (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (IH Rx lx Mx MD T q n da nd db lo v m2 c1 b1 (ci + 1) (B + 8) H' fin rdD Hh) end;
    try zreg; try lia; try eassumption.
  intros R' ci' B' H'' G26 G7 G21 G10 G13 G20 G31 G23 G22 G24 X0 X1 X2 X3 X4 X5 X6 X7 HK.
  eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chainT HK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma x_loop_d {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n ext c0 b0 ci B H : Z) (fin : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA6 = ext -> zget_l Rb l kA2 = n - c0 -> zget_l Rb l kS10 = q + c0 -> zget_l Rb l kS2 = b0 ->
  zget_l Rb l kS8 = n - ci -> zget_l Rb l kA7 = q + ci -> zget_l Rb l kT0 = q + ci ->
  zget_l Rb l kA1 = B -> zget_l Rb l kA5 = B -> zget_l Rb l kS4 = H ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < ext -> ext <= 15 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  (* [comment removed for export] *)
  (forall R' (H' : Z),
     zget R' kS4 = H' -> zget R' kS8 = 0 -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_XDT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_XD_T (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' (ci' B' H' : Z),
     zget R' kA3 = q + ci' -> zget R' kT0 = q + ci' -> zget R' kS8 = n - ci' -> zget R' kA1 = B' -> zget R' kA5 = B' -> zget R' kS4 = H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> ext <= B' -> B' <= 22 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_XDT ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DXE8_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DXLOOP_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n ext c0 b0 ci B H fin Hh La6 La2 Ls9 Ls1 Ls7 La7 Lt0 La1 La5 Ls3
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt Hext HH1 HH2 HBc Hq1 Hn26 Hq2 Hin Rfin KX KD; [lia|].
  zkeys. unfold L_DXLOOP_T, L_DXE8_T, L_LVX_XD_T in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB. pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b0 + 8 * (n - c0)) with B by lia. lia.
    - keptc_closeT. }
  zbr Rfd false.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.                   (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  assert (HH' : 0 <= H + fin ci * 2 ^ B < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia).
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z_lt_dec (B + 8) ext) as [Hmore | Hdone].
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n ext c0 b0 (ci + 1) (B + 8) (H + fin ci * 2 ^ B) fin Hh) end;
      try zreg; try lia; try eassumption.
    intros R' ci' B' H'' G14 G6 G24 G12 G16 G20 X0 X1 X2 X3 X4 X5 X6 X7 HK.
    eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chainT HK.
  - zbr Rfd false.
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (H + fin ci * 2 ^ B)) end;
      try zreg; try lia. keptc_closeT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_L1T : list positive := [2; 3; 4; 5; 9; 10; 20; 21; 22; 23; 24; 26]%positive.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stub_L1_t {RCa1 : RunCtx}  : forall (pc : Z) Rb l M MD T (q n c0 b0 u rv : Z),
  ((pc = L_LVX_L1_T /\ zget_l Rb l kT6 = Z.shiftl (n - c0) 32) \/ (pc = L_LVX_LL1_T /\ zget_l Rb l kT5 = Z.shiftl (n - c0) 32)) ->
  m_halted MD = None ->
  zget_l Rb l kS8 = n - c0 -> zget_l Rb l kS10 = q + c0 -> zget_l Rb l kS2 = b0 -> zget_l Rb l kSP = u + -256 -> zget_l Rb l kS1 = u ->
  0 <= n - c0 -> n - c0 < 536870912 -> 0 <= q + c0 -> q + n < 18446744073709551616 -> 0 <= b0 -> b0 + 8 * (n - c0) < 18446744073709551616 ->
  0 <= u + -1024 -> u + 208 <= 18446744073709551616 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -184) rv -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -120) 0 ->   (* [comment removed for export] *)
  (forall R', zget R' kS10 = q + n -> zget R' kS8 = 0 -> zget R' kS2 = b0 + 8 * (n - c0) -> zget R' kS11 = rv ->
     zget R' kA3 = u -> zget R' kA1 = 0 ->
     keptc Rb l R' KS_L1T -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  intros pc Rb l M MD T q n c0 b0 u rv Hpc Hh Ls7 Ls9 Ls1 Lsp Ls0 H1 H2 H3 H4 H5 H6 Hu1 Hu2 Hrv Hfl K.
  zkeys. unfold L_LVX_L1_T, L_LVX_LL1_T, L_LEAVE in *. pose proof two64_eq as TW64.
  destruct Hpc as [[-> Lt] | [-> Lt]];
    [ zstep Rfd; zext32;              (* [comment removed for export] *)
      zstep Rfd                       (* [comment removed for export] *)
    | zstep Rfd; zext32 ];            (* [comment removed for export] *)
  (
    zstep Rfd;                        (* [comment removed for export] *)
    zsetreg (8 * (n - c0)) ltac:(symmetry; apply shl_3);
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg;
    cbv [keptc KS_L1T]; split_conj; try exact I; zreg).
Qed.

(* [comment removed for export] *)
Definition L_LVX_XL_T : Z := 96184.  (* [comment removed for export] *)
Definition KS_XST : list positive := [2; 3; 4; 5; 9; 10; 20; 21; 25]%positive.   (* [comment removed for export] *)
Lemma stub_X_t {RCa1 : RunCtx}  : forall (pc : Z) Rb l M MD T (q n c0 b0 : Z),
  ((pc = L_LVX_XD_T /\ zget_l Rb l kS10 = q + c0) \/ (pc = L_LVX_XL_T /\ zget_l Rb l kA4 = q + c0)) ->
  m_halted MD = None ->
  zget_l Rb l kA2 = n - c0 -> zget_l Rb l kS2 = b0 ->
  0 <= n - c0 -> n - c0 < 536870912 -> 0 <= q + c0 -> q + n < 18446744073709551616 -> 0 <= b0 -> b0 + 8 * (n - c0) < 18446744073709551616 ->
  (forall R', zget R' kS10 = q + n -> zget R' kS2 = b0 + 8 * (n - c0) ->
     keptc Rb l R' KS_XST -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD2 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  intros pc Rb l M MD T q n c0 b0 Hpc Hh La2 Ls1 H1 H2 H3 H4 H5 H6 K.
  zkeys. unfold L_LVX_XD_T, L_LVX_XL_T, L_LEAVE_LD2 in *. pose proof two64_eq as TW64.
  destruct Hpc as [[-> Lx] | [-> Lx]]; (
    zstep Rfd;                        (* [comment removed for export] *)
    zsetreg (8 * (n - c0)) ltac:(symmetry; apply shl_3);
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd; zext32;                (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    zstep Rfd;                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg;
    cbv [keptc KS_XST]; split_conj; try exact I; zreg).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tabsP {RCa1 : RunCtx}  (cx : ictx) (st : ist) (cf : Z -> Z) (M : mem) (na nd : Z) : Prop :=
  let la := cp_addr cx (t_lc st) in let da := cp_addr cx (t_dc st) in
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M la na (rdc cf (t_lc st)) /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M da nd (rdc cf (t_dc st)) /\
  tab_ok LENS (rdc cf (t_lc st)) (t_lb st) na = true /\ tab_ok DISTS (rdc cf (t_dc st)) (t_db st) nd = true /\
  0 < la /\ la + 4 * na <= c_zc cx /\ 0 < da /\ da + 4 * nd <= c_zc cx /\ na <= 2048 /\ nd <= 2048 /\
  la mod 2 = 0 /\ da mod 2 = 0 /\
  ZSEP (la + 4 * na <= c_ob cx \/ c_ob cx + c_osz cx <= la) /\ ZSEP (la + 4 * na <= c_p cx \/ c_p cx + 1384 <= la) /\
  ZSEP (da + 4 * nd <= c_ob cx \/ c_ob cx + c_osz cx <= da) /\ ZSEP (da + 4 * nd <= c_p cx \/ c_p cx + 1384 <= da) /\
  ZSEP (la + 4 * na <= c_p cx + 7160 \/ c_p cx + 7176 <= la) /\ ZSEP (da + 4 * nd <= c_p cx + 7160 \/ c_p cx + 7176 <= da) /\
  (65536 <= c_p cx -> 65536 <= la /\ 65536 <= da).

Lemma live_tabs {RCa1 : RunCtx}  : forall cx st lf cf M,
  ctx_ok ROMHI_T cx -> RNG cx st lf cf -> tables_live cx st cf -> rom_ok M ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  exists na nd, tabsP cx st cf M na nd.
Proof.
  intros cx st lf cf M CX R TL ROM Hcodes.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  pose proof (sep_p_ob ROMHI_T _ SEP) as Spob. pose proof (sep_p_rom ROMHI_T _ SEP) as Sprom.
  icx_cbn. cbv [STATE_SIZE ROM_LO_ALL ROMHI_T] in Spob, Sprom.
  dand AL as (ALu & ALp & ALw). icx_cbn.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold RNG in R; icx_cbn; cbv [N_CODES N_LENS] in R; destr_conj R.
  unfold tables_live in TL. unfold tabsP. icx_cbn. cbv [N_CODES ] in *.
  destruct lc as [o1 | |]; destruct dc as [o2 | |]; try contradiction.
  - (* [comment removed for export] *)
    dand TL as (Ho1 & Hlb & Hdb & Ho2 & Ho2nx & Hnx & TOKL & TOKD). subst o1.
    exists o2, (nx - o2). unfold cp_addr, rdc. icx_cbn. cbv [o_codes].
    split_conj; try assumption; try (unfold ZSEP; lia).
    + replace (p + 1384 + 4 * 0) with (p + 1384 + 4 * 0) by lia.
      exact (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 4 M (p + 1384) 1444 cf 0 o2 Hcodes ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 4 M (p + 1384) 1444 cf o2 (nx - o2) Hcodes ltac:(lia) ltac:(lia) ltac:(lia)).
    + clear - ALp. Z.to_euclidean_division_equations; lia.
    + clear - ALp Ho2. Z.to_euclidean_division_equations; lia.
  - (* [comment removed for export] *)
    destruct TL as [Hlb Hdb]. subst lb db.
    exists 512, 32. unfold cp_addr, rdc. cbv [LENFIX_ADDR DISTFIX_ADDR].
    split_conj; try exact lenfix_ok; try exact distfix_ok; try (unfold ZSEP; lia).
    + apply (mem_arr_ext (run_segments R_segs rc_inp rc_sp rc_mb) 4 M 67422 512 lenfix_f). { exact (rom_lenfix_arr M ROM). } exact lenfix_f_model.
    + apply (mem_arr_ext (run_segments R_segs rc_inp rc_sp rc_mb) 4 M 69470 32 distfix_f). { exact (rom_distfix_arr M ROM). } exact distfix_f_model.
    + reflexivity.
    + reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac st_rest_set_tac :=
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_w3 in *; icx_cbn;
  pose proof two64_eq as TW64;
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17);
  repeat split;
  first [ apply mem_u32_stored; clear - Hp1 Hp2; lia_std
        | (apply mem_u64_frame || apply mem_u32_frame); [assumption | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std] ].
Lemma st_rest_set92 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st v (t_offset st) (t_extra st)) (wbytes M (w64 (c_p cx + 108)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Lemma st_rest_set96 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st (t_length st) v (t_extra st)) (wbytes M (w64 (c_p cx + 112)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Lemma st_rest_set100 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st (t_length st) (t_offset st) v) (wbytes M (w64 (c_p cx + 116)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
