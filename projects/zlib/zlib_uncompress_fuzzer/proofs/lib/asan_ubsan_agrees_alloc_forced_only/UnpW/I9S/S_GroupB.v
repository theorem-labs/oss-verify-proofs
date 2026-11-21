(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S Require SBase.

Module S_ClDefs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
Definition L_CL_HEAD : Z := 88624.    (* [comment removed for export] *)
Definition L_CL_DONE : Z := 89224.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition s_regs_cl (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\ zget_l Rb l kS11 = c_q cx + t_cin st /\ zget_l Rb l kA3 = t_shave st.

Definition clhead_stmt : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = CODELENS -> sinv cx st lf cf ->
    s_regs_cl cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes R_segs (zcfg R_segs L_CL_HEAD (zupd Rb l) M MD) T.

(* [comment removed for export] *)
Definition s_regs_cld (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\ zget_l Rb l kS11 = c_q cx + t_cin st /\
  zget_l Rb l kA2 = t_nlen st /\ zget_l Rb l kA4 = t_nlen st + t_ndist st.

Definition cldone_stmt : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = CODELENS -> t_nlen st + t_ndist st <= t_shave st -> sinv cx st lf cf ->
    s_regs_cld cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes R_segs (zcfg R_segs L_CL_DONE (zupd Rb l) M MD) T.
End FXG.
End S_ClDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Inftrees InftreesCoverage ItCovIface InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require ItBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S Require S_Type S_LenF.

Module S_TableL.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_TAB_LOOP : Z := 87380.   (* [comment removed for export] *)
Definition L_TAB_BODY : Z := 88204.   (* [comment removed for export] *)
Definition L_LL_BODY : Z := 88336.    (* [comment removed for export] *)
Definition L_LL_HEAD : Z := 88384.    (* [comment removed for export] *)
Definition L_LL_FILL0 : Z := 88428.   (* [comment removed for export] *)
Definition L_LL_FLOOP : Z := 88468.   (* [comment removed for export] *)
Definition L_LL_FEND : Z := 88504.    (* [comment removed for export] *)
Definition A_ORDER : Z := 67132.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KS_LL : list positive := [2; 3; 4; 5; 9; 11; 12; 19; 20; 21; 22; 23; 24; 27; 30; 31; 32]%positive.
(* [comment removed for export] *)
Definition KS_TB : list positive := [2; 3; 4; 5; 9; 11; 12; 19; 20; 21; 22; 23; 24; 30; 31; 32]%positive.
(* [comment removed for export] *)
Definition KS_LF : list positive := [2; 3; 4; 5; 9; 10; 11; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 30; 31; 32]%positive.
End FXG.
Ltac keptc_close ::= cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF]; split_conj; try exact I; zreg.
Ltac keptc_chain HK ::= cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zext32_shift31 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) (31 mod 64) = 2 * x.
Proof.
  intros x Hx. change (31 mod 64) with 31. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia_std.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia_std).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia_std. lia_std.
Qed.
(* [comment removed for export] *)
Lemma shiftl_1m : forall x, Z.shiftl x (1 mod 64) = 2 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia_std. change (2 ^ (1 mod 64)) with 2. lia_std. Qed.
(* [comment removed for export] *)
Lemma land7_range : forall h, 0 <= Z.land h 7 < 8.
Proof. intros. apply land_7. Qed.
(* [comment removed for export] *)
Lemma drop3_bound : forall H B, 0 <= H < 2 ^ B -> 3 <= B -> 0 <= H / 2 ^ 3 < 2 ^ (B - 3).
Proof. intros H B HH HB. apply hold_shr_bound; lia_std. Qed.

(* [comment removed for export] *)
Lemma land_m32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia_std. apply Z.mod_small. exact Hx. Qed.

(* [comment removed for export] *)
Lemma order_f_lt : forall i, 0 <= i < 19 -> 0 <= order_f i < 65536.
Proof. intros i Hi. pose proof (order_f_range i Hi). lia_std. Qed.

(* [comment removed for export] *)
End FXG.
Ltac zside1 := first [reflexivity | exact I | zlia].
Ltac tstoreP fd HP HPres :=
  let pc := zpc in
  fd pc ltac:(fun F E D =>
    lazymatch type of D with
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply zu_sd; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    end);
  lazymatch goal with
  | |- realizes _ (zcfg _ _ _ (wbytes ?M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
      (let HP' := fresh in pose proof (HPres M _ a v HP ltac:(zside1) ltac:(zside1)) as HP'; clear HP; rename HP' into HP);
      zmem_post_arr; zmem_post
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
(* [comment removed for export] *)
End FXG.
Ltac tstore_arrP2 fd Ha i HP HPres :=
  lazymatch type of Ha with
  | mem_arr ?k ?segs ?M ?base ?n ?f =>
      let pc := zpc in
      fd pc ltac:(fun F E D =>
        lazymatch type of D with
        | decode_any _ = Some (Store SZ1 _ _ _, _) =>
            eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ2 _ _ _, _) =>
            eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ4 _ _ _, _) =>
            eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        end);
      lazymatch goal with
      | |- realizes _ (zcfg _ _ _ (wbytes M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
          apply (mem_arr_upd segs k M base n f a i v) in Ha; [| zlia | zlia];
          (let kn := eval cbv in (Z.to_nat k) in change (Z.to_nat k) with kn in Ha);
          (let HP' := fresh in pose proof (HPres M _ a v HP ltac:(zside1) ltac:(zside1)) as HP'; clear HP; rename HP' into HP);
          repeat match goal with
          | H : mem_arr ?k' segs M ?base' ?n' ?f' |- _ =>
              first [ apply (mem_arr_frame segs k' M base' n' f' a (Z_to_le_bytes kk v)) in H; [|unfold zdisj; zlen_norm; zlia]
                    | idtac "tstore_arrP2: mem_arr fact dropped at array store" a; clear H ]
          end;
          zmem_post
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
(* [comment removed for export] *)
End FXG.
Ltac keptc_trans :=
  repeat match goal with H : keptc _ _ _ _ |- _ => cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF] in H; destr_conj H end;
  cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF]; split_conj; try exact I;
  rewrite ?zget_zupd in *; cbv [zget_l] in *; cbn [alookup Pos.eqb] in *;
  first [ assumption | reflexivity
        | etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lenlens_loop : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T
    (p q n ncode j ci B H : Z) (fin lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kS0 = p -> zget_l Rb l kRA = p + 168 ->
  zget_l Rb l kA3 = A_ORDER + 2 * j -> zget_l Rb l kA4 = ncode - j -> zget_l Rb l kA5 = j + 1 -> zget_l Rb l kA2 = ncode ->
  zget_l Rb l kS1 = B -> zget_l Rb l kS8 = H -> zget_l Rb l kS9 = n - ci -> zget_l Rb l kS11 = q + ci ->
  ncode - j <= Z.of_nat N -> 0 <= j -> j < ncode -> ncode <= 19 ->
  0 <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) -> ZSEP (p + 7176 <= 65536 \/ 135168 <= p) ->
  mem_wr R_segs M p 7176 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 2 R_segs M A_ORDER 19 order_f ->
  mem_arr 2 R_segs M (p + 168) 320 lf -> (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) ->
  (forall i, 0 <= i < j -> lf (order_f i) <= 7) ->
  P j M ->
  (forall M' jo (a v : Z), P jo M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' jo (a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (* [comment removed for export] *)
  (forall R' M' (j' B' H' : Z) (lf' : Z -> Z),
     zget R' kS1 = B' -> zget R' kS8 = H' -> zget R' kS9 = 0 -> zget R' kS11 = q + n ->
     j <= j' -> j' < ncode -> 0 <= B' -> B' < 3 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * n ->
     B' + 3 * (j' - j) = 8 * (n - ci) + B ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 2 R_segs M' A_ORDER 19 order_f ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < j' -> lf' (order_f i) <= 7) -> P j' M' ->
     keptc Rb l R' KS_LL ->
     realizes R_segs (zcfg R_segs L_LEAVE_LD (zupd R' []) M' MD) T) ->
  (* [comment removed for export] *)
  (forall R' M' (ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kS1 = B' -> zget R' kS8 = H' -> zget R' kS9 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kA2 = ncode ->
     zget R' kS0 = p -> zget R' kRA = p + 168 ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' + 3 * (ncode - j) = 8 * (n - ci) + B ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 2 R_segs M' A_ORDER 19 order_f ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < ncode -> lf' (order_f i) <= 7) -> P ncode M' ->
     keptc Rb l R' KS_LL ->
     realizes R_segs (zcfg R_segs L_LL_FILL0 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_LL_HEAD (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T p q n ncode j ci B H fin lf Hh L26 L2 La3 La4 La5 La2 Ls0 Ls7 Ls8 Ls10
    HN Hj0 Hj1 Hnc Hc0 Hc1 HB0 HB1 HH0 HH1 HBc Hq1 Hn26 Hq2 Hp1 Hp2 SPQ SPR Wp Hin Rfin Hord Hlens Rlf Hlf7 HP HPa HPb KX KD; [lia|].
  zkeys. unfold L_LL_HEAD, L_LL_FILL0, L_LEAVE_LD, A_ORDER in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  zstep Rfd.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (BODY : forall RJ (cib Hb Bb : Z),
    zget RJ kS0 = p -> zget RJ kRA = p + 168 ->
    zget RJ kA3 = 67132 + 2 * j -> zget RJ kA4 = ncode - j -> zget RJ kA5 = j + 1 -> zget RJ kA2 = ncode ->
    zget RJ kS1 = Bb -> zget RJ kS8 = Hb -> zget RJ kS9 = n - cib -> zget RJ kS11 = q + cib ->
    ci <= cib -> cib <= n -> 3 <= Bb -> Bb <= 40 -> 0 <= Hb -> Hb < 2 ^ Bb -> Bb <= 8 * cib ->
    8 * (n - cib) + Bb = 8 * (n - ci) + B ->
    keptc Rb l RJ KS_LL ->
    realizes R_segs (zcfg R_segs L_LL_BODY (zupd RJ []) M MD) T).
  { intros RJ cib Hb Bb G26 G2 G14 G15 G16 G13 G9 G24 G25 G27 X1 X2 X3 X4 X5 X6 X7 X8 HK.
    unfold L_LL_BODY. zkeys.
    pose proof (pow2_48 Bb ltac:(lia)) as HPBb.
    pose proof (land7_range Hb) as Hv.
    pose proof (order_f_range j ltac:(lia)) as Ho. pose proof (order_f_lt j ltac:(lia)) as Ho2.
    zstep Rfd.                        (* [comment removed for export] *)
    tstoreP Rfd HP HPa.               (* [comment removed for export] *)
    tstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (Hb / 2 ^ 3) ltac:(symmetry; apply (srl_hold Hb Bb 3); lia).
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (2 * order_f j) ltac:(rewrite shiftl_1m; reflexivity).
    zstep Rfd.                        (* [comment removed for export] *)
    tstore_arrP2 Rfd Hlens (order_f j) HP HPb. (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (drop3_bound Hb Bb ltac:(lia) ltac:(lia)) as Hd3.
    assert (Rlf1 : forall i, 0 <= i < 320 -> 0 <= zfupd lf (order_f j) (Z.land Hb 7) i < 65536).
    { intros i Hi. unfold zfupd. destruct (Z.eqb_spec i (order_f j)); [lia | apply Rlf; lia]. }
    assert (Hlf7' : forall i, 0 <= i < j + 1 -> zfupd lf (order_f j) (Z.land Hb 7) (order_f i) <= 7).
    { intros i Hi. unfold zfupd. destruct (Z.eqb_spec (order_f i) (order_f j)); [lia|]. apply Hlf7.
      destruct (Z.eq_dec i j); [subst; congruence | lia]. }
    destruct (Z.eq_dec (ncode - j) 1) as [Hlast | Hmore].
    - zbr Rfd true.                   (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KD Rx Mx cib (Bb - 3) (Hb / 2 ^ 3) (zfupd lf (order_f j) (Z.land Hb 7))) end;
        try zreg; try assumption; try lia.
      + intros i Hi. apply Hlf7'. lia.
      + replace ncode with (j + 1) by lia. exact HP.
      + keptc_trans.
    - zbr Rfd false.                  (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (IH P Rx lx Mx MD T p q n ncode (j + 1) cib (Bb - 3) (Hb / 2 ^ 3) fin (zfupd lf (order_f j) (Z.land Hb 7)) Hh) end;
        try zreg; try assumption; try lia.
      + intros R' M' j' B' H' lf'. intros. eapply (KX R' M' j' B' H' lf'); try eassumption; try lia.
        keptc_trans.
      + intros R' M' ci' B' H' lf'. intros. eapply (KD R' M' ci' B' H' lf'); try eassumption; try lia.
        keptc_trans. }
  destruct (Z_lt_dec 2 B) as [HB3 | HB3].
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (BODY Rx ci H B) end; try zreg; try lia. keptc_close.
  - zbr Rfd false.
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
    + zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KX Rx Mx j B H lf) end;
        try zreg; try assumption; try lia. keptc_close.
    + zbr Rfd true.                   (* [comment removed for export] *)
      pose proof (Rfin ci ltac:(lia)) as Rb1.
      tld1 Hin ci Rfin.               (* [comment removed for export] *)
      tstep1 Rfd.                     (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hpl0 Hpl1].
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (B + 8) ltac:(symmetry; apply lor8_small; lia).
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (BODY Rx (ci + 1) (fin ci * 2 ^ B + H) (B + 8)) end;
        try zreg; try lia.
      keptc_close.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fill_loop : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T (p j jo : Z) (lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kRA = p + 168 -> zget_l Rb l kA0 = 4294967295 -> zget_l Rb l kA1 = A_ORDER + 2 * j -> zget_l Rb l kA5 = j + 1 ->
  19 - j <= Z.of_nat N -> 0 <= j -> j < 19 ->
  0 < p -> p + 7176 <= 140737488355328 -> ZSEP (p + 7176 <= 65536 \/ 135168 <= p) ->
  mem_wr R_segs M p 7176 -> mem_arr 2 R_segs M A_ORDER 19 order_f ->
  mem_arr 2 R_segs M (p + 168) 320 lf -> (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) ->
  (forall i, 0 <= i < j -> lf (order_f i) <= 7) ->
  P jo M ->
  (forall M' jo' (a v : Z), P jo' M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo' (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (lf' : Z -> Z),
     zget R' kA2 = 19 ->
     mem_wr R_segs M' p 7176 -> mem_arr 2 R_segs M' A_ORDER 19 order_f ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < 19 -> lf' (order_f i) <= 7) -> P jo M' ->
     keptc Rb l R' KS_LF ->
     realizes R_segs (zcfg R_segs L_LL_FEND (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_LL_FLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T p j jo lf Hh L2 La0 La1 La5 HN Hj0 Hj1 Hp1 Hp2 SPR Wp Hord Hlens Rlf Hlf7 HP HPb K; [lia|].
  zkeys. unfold L_LL_FLOOP, L_LL_FEND, A_ORDER in *. pose proof two64_eq as TW64.
  pose proof (order_f_range j ltac:(lia)) as Ho. pose proof (order_f_lt j ltac:(lia)) as Ho2.
  assert (Rord : forall i, 0 <= i < 19 -> 0 <= order_f i < 65536) by (intros; apply order_f_lt; lia).
  tstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (j + 1) ltac:(symmetry; apply land_m32; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 * order_f j) ltac:(rewrite shiftl_1m; reflexivity).
  zstep Rfd.                          (* [comment removed for export] *)
  tstore_arrP2 Rfd Hlens (order_f j) HP HPb. (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  assert (Rlf1 : forall i, 0 <= i < 320 -> 0 <= zfupd lf (order_f j) 0 i < 65536).
  { intros i Hi. unfold zfupd. destruct (Z.eqb_spec i (order_f j)); [lia | apply Rlf; lia]. }
  assert (Hlf7' : forall i, 0 <= i < j + 1 -> zfupd lf (order_f j) 0 (order_f i) <= 7).
  { intros i Hi. unfold zfupd. destruct (Z.eqb_spec (order_f i) (order_f j)); [lia|]. apply Hlf7.
    destruct (Z.eq_dec i j); [subst; congruence | lia]. }
  destruct (Z.eq_dec j 18) as [Hlast | Hmore].
  - zbr Rfd false.                    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd lf (order_f j) 0)) end;
      try zreg; try assumption.
    + intros i Hi. apply Hlf7'. lia.
    + keptc_close.
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T p (j + 1) jo (zfupd lf (order_f j) 0) Hh) end;
      try zreg; try assumption; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma table_loop : forall (k : nat) Rb l M MD T (q n cinj holdj j : Z) (fin : Z -> Z),
  m_halted MD = None -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  14 - 8 * Z.of_nat k <= j < 22 - 8 * Z.of_nat k -> (1 <= k <= 2)%nat -> 0 <= j ->
  0 <= cinj <= n -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  zget_l Rb l kS1 = j -> zget_l Rb l kA2 = j ->
  zget_l Rb l kS11 = q + cinj -> zget_l Rb l kS9 = n - cinj -> zget_l Rb l kS8 = holdj ->
  mem_arr 1 R_segs M q n fin ->
  (forall R' hold' j',   (* [comment removed for export] *)
     zget R' kS11 = q + n -> zget R' kS9 = 0 -> zget R' kS8 = hold' -> zget R' kS1 = j' ->
     j' = j + 8 * (n - cinj) -> 0 <= hold' < 2 ^ j' -> n - cinj < Z.of_nat k ->
     keptc Rb l R' KS_TB ->
     realizes R_segs (zcfg R_segs L_LEAVE_LD (zupd R' []) M MD) T) ->
  (forall R' hold' j',   (* [comment removed for export] *)
     zget R' kS10 = q + cinj + Z.of_nat k -> zget R' kS11 = q + cinj + Z.of_nat k ->
     zget R' kS9 = n - cinj - Z.of_nat k -> zget R' kS8 = hold' -> zget R' kS1 = j' ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= n - cinj ->
     keptc Rb l R' KS_TB ->
     realizes R_segs (zcfg R_segs L_TAB_BODY (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_TAB_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros Rb l M MD T q n cinj holdj j fin Hh Hfin Hj Hk Hj0 Hc Hhj Hjc Hq1 Hn26 Hq2 L9 L13 L27 L25 L24 Hin KLV KDN; [lia|].
  zkeys. unfold L_TAB_LOOP, L_TAB_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
  assert (Hj40 : 2 ^ j <= 2 ^ 21) by (apply Z.pow_le_mono_r; lia). change (2 ^ 21) with 2097152 in Hj40.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  - (* [comment removed for export] *)
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end; try zreg; try lia.
    all: first [ keptc_close | replace (j + 8 * (n - cinj)) with j by lia; lia ].
  - zbr Rfd true.                     (* [comment removed for export] *)
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (fin cinj * 2 ^ j) ltac:(rewrite (Z.mod_small j) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    destruct k as [|k'].
    + (* [comment removed for export] *)
      zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj) (j + 8)) end; try zreg; try lia.
      keptc_close.
    + zbr Rfd true.                   (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH R' l' M MD T q n (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) fin Hh Hfin) end;
        [ lia | lia | lia | lia | lia | lia | lia | lia | lia | zreg .. | exact Hin | | ].
      * intros R' hold' j'. intros. eapply KLV; try eassumption; try lia.
      * intros R' hold' j'. intros. eapply KDN; try eassumption; try lia.
Qed.
End FXG.
End S_TableL.

Module S_Table.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ItCovIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.ItBridge.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_DistL S_TableL S_ClDefs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_TAB_SKIP : Z := 88200.   (* [comment removed for export] *)
Definition L_LL_SETUP : Z := 88292.   (* [comment removed for export] *)
Definition L_LL_FILL : Z := 88432.    (* [comment removed for export] *)
Definition L_LL_TABLE : Z := 88508.   (* [comment removed for export] *)
Definition L_LL_RET : Z := 88560.     (* [comment removed for export] *)
Definition L_TBLERR : Z := 89864.     (* [comment removed for export] *)
Definition L_BAD_TAB : Z := 89316.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_u64_eqv : forall M a v v', v = v' -> mem_u64 R_segs M a v -> mem_u64 R_segs M a v'.
Proof. intros M a v v' <- H. exact H. Qed.
Lemma mem_u64_mod : forall M a v, mem_u64 R_segs M a v -> mem_u64 R_segs M a (v mod 18446744073709551616).
Proof. intros M a v H. unfold mem_u64 in *. change 18446744073709551616 with two64. rewrite Z_to_le_bytes_mod by lia_std. exact H. Qed.

(* [comment removed for export] *)
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
Lemma land31_mod : forall h, 0 <= h -> Z.land h 31 = h mod 32.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma bits_54_59 : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 54 mod 18446744073709551616) 59 = (h / 32) mod 32.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 54) with 18014398509481984. change (2 ^ 59) with 576460752303423488. nia.
Qed.
Lemma bits_50_60 : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 50 mod 18446744073709551616) 60 = (h / 1024) mod 16.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 50) with 1125899906842624. change (2 ^ 60) with 1152921504606846976. nia.
Qed.
Lemma mod_range : forall a m, 0 < m -> 0 <= a mod m < m.
Proof. intros. apply Z.mod_pos_bound. assumption. Qed.
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
Lemma it_fail_shape : forall ty lens lens_ofs codes tbl table bits work,
  let r := inflate_table ty lens lens_ofs codes tbl table bits work in
  it_ret r <> 0 -> it_table r = table /\ it_bits r = bits.
Proof. intros. apply inflate_table_fail_shape. assumption. Qed.

(* [comment removed for export] *)
Lemma order_covers : forall (lf : Z -> Z) b,
  (forall j, 0 <= j < 19 -> lf (order_f j) <= b) -> forall i, 0 <= i < 19 -> lf i <= b.
Proof.
  intros lf b H i Hi.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
              i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18) by lia_std.
  decompose [or] C; subst;
    [ change (lf 0) with (lf (order_f 3))
    | change (lf 1) with (lf (order_f 17))
    | change (lf 2) with (lf (order_f 15))
    | change (lf 3) with (lf (order_f 13))
    | change (lf 4) with (lf (order_f 11))
    | change (lf 5) with (lf (order_f 9))
    | change (lf 6) with (lf (order_f 7))
    | change (lf 7) with (lf (order_f 5))
    | change (lf 8) with (lf (order_f 4))
    | change (lf 9) with (lf (order_f 6))
    | change (lf 10) with (lf (order_f 8))
    | change (lf 11) with (lf (order_f 10))
    | change (lf 12) with (lf (order_f 12))
    | change (lf 13) with (lf (order_f 14))
    | change (lf 14) with (lf (order_f 16))
    | change (lf 15) with (lf (order_f 18))
    | change (lf 16) with (lf (order_f 0))
    | change (lf 17) with (lf (order_f 1))
    | change (lf 18) with (lf (order_f 2)) ];
    apply H; lia_std.
Qed.

(* [comment removed for export] *)
Lemma le_cell2_range : forall bs i, 0 <= le_cell 2 bs i < 65536.
Proof.
  intros bs i. unfold le_cell.
  set (l := firstn (Z.to_nat 2) (skipn (Z.to_nat (2 * i)) bs)).
  pose proof (bytes_le_to_Z_bound l) as R. pose proof (bytes_le_to_Z_nonneg l) as R0.
  assert (L : (length l <= 2)%nat) by (subst l; rewrite length_firstn; cbn; lia_std).
  assert (P : 2 ^ (8 * Z.of_nat (length l)) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia_std).
  change (2 ^ 16) with 65536 in P. lia_std.
Qed.
Lemma work_arr : forall M p, mem_wr R_segs M p 7176 -> 0 <= p -> p + 7176 <= two64 ->
  exists wf, mem_arr 2 R_segs M (p + 808) 288 wf /\ (forall i, 0 <= i < 288 -> 0 <= wf i < 65536).
Proof.
  intros M p W Hp1 Hp2.
  destruct (mem_wr_readable R_segs wr_rd_R M (p + 808) 576 ltac:(eapply mem_wr_sub; [exact W | lia_std | lia_std]) ltac:(lia_std)) as [bs [A B]].
  exists (le_cell 2 bs). split.
  - apply (mem_arr_of_bytes R_segs 2 M (p + 808) 288 bs A); try lia_std.
  - intros i _. apply le_cell2_range.
Qed.

(* [comment removed for export] *)
Lemma rom_it_tabs : forall M, rom_ok M ->
  mem_arr 2 R_segs M LBASE_ADDR 31 (arr_get lbase_a) /\ mem_arr 2 R_segs M LEXT_ADDR 31 (arr_get lext_a) /\
  mem_arr 2 R_segs M DBASE_ADDR 32 (arr_get dbase_a) /\ mem_arr 2 R_segs M DEXT_ADDR 32 (arr_get dext_a).
Proof.
  intros M H. cbv [LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR]. split_conj.
  - eapply mem_arr_ext; [apply rom_lbase_arr; exact H | intros; apply lbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_lext_arr; exact H | intros; apply lext_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dbase_arr; exact H | intros; apply dbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dext_arr; exact H | intros; apply dext_f_model; assumption].
Qed.

(* [comment removed for export] *)
Lemma i_frame_slots : forall cx M, i_frame cx M ->
  mem_u64 R_segs M (c_u cx + -216) (c_p cx + 1384) /\ mem_u64 R_segs M (c_u cx + -200) (c_p cx + 160) /\
  mem_u64 R_segs M (c_u cx + -224) (c_p cx + 136) /\ mem_u64 R_segs M (c_u cx + -208) (c_p cx + 808) /\
  mem_u64 R_segs M (c_u cx + -120) (c_u cx) /\ mem_u64 R_segs M (c_u cx + -128) 0 /\
  mem_u64 R_segs M (c_u cx + -144) (-16180) /\ mem_u64 R_segs M (c_u cx + -232) (c_p cx + 140) /\
  mem_u64 R_segs M (c_u cx + -152) (c_p cx + 168) /\ mem_u64 R_segs M (c_u cx + -136) JTAB_ADDR.
Proof. intros cx M H. unfold i_frame in H. destr_conj H. split_conj; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_sh (st : ist) (j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).
(* [comment removed for export] *)
Definition st_ll (st : ist) (ci H B j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).
(* [comment removed for export] *)
Definition st_ct (st : ist) (m rv lb nx sh : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) rv
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) (CDyn 0) lb (t_db st)   (* a worker 1.4: LENLENS sets distcode with lencode (smodel14-r1) *)
      (t_ncode st) (t_nlen st) (t_ndist st) sh nx (t_whave st) (t_wnext st).
(* [comment removed for export] *)
Definition st_lt (st : ist) (lb nx : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) (CDyn 0) lb (t_db st)   (* a worker 1.4: distcode with lencode *)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) nx (t_whave st) (t_wnext st).
(* [comment removed for export] *)
Definition st_tb (st : ist) (m ci H B ncode nlen ndist sh : Z) : ist :=
  IST m (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      ncode nlen ndist sh (t_nx st) (t_whave st) (t_wnext st).

End FXG.
Ltac ist_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
Lemma sinv_ll : forall cx st lf cf ci H B j lf',
  sinv cx st lf cf -> t_mode st = LENLENS ->
  t_cin st <= ci -> ci <= c_n cx -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= j -> j <= 19 ->
  (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j -> lf' (order_f i) <= 7) ->
  sinv cx (st_ll st ci H B j) lf' cf /\ meas cx (st_ll st ci H B j) <= meas cx st.
Proof.
  intros cx st lf cf ci H B j lf' (R & W & P & Mo) Hm H1 H2 H3 H4 H5 H6 H7 H8 Hj0 Hj1 Rlf' Hlf'.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_ll, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. cbv [N_LENS N_CODES] in R. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (ML : LENLENS = LENLENS -> 4 <= ncode /\ ncode <= 19 /\ shave <= 19 /\ 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\
            (forall j0, 0 <= j0 < shave -> lf (arr_get order_a j0) <= 7)) by mode_get Mo.
  specialize (ML eq_refl). dand ML as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear Mo.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1 H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [intros _; split_conj; try assumption; intros j0 Hj; rewrite <- order_f_model by lia_std; apply Hlf'; exact Hj |].
    split_conj; mode_vacuous.
  - clear - H8. lia_std.
Qed.

(* [comment removed for export] *)
Lemma sinv_ll_ct : forall cx st lf cf cf' lb nx,
  sinv cx st lf cf -> t_mode st = LENLENS ->
  1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= N_CODES -> tab_ok CODES (rdc cf' (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_ct st CODELENS 0 lb nx 0) lf cf' /\ meas cx (st_ct st CODELENS 0 lb nx 0) < meas cx st.
Proof.
  intros cx st lf cf cf' lb nx (R & W & P & Mo) Hm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb0 db ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_ct, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (ML : LENLENS = LENLENS -> 4 <= ncode /\ ncode <= 19 /\ shave <= 19 /\ 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\
            (forall j0, 0 <= j0 < shave -> lf (arr_get order_a j0) <= 7)) by mode_get Mo.
  specialize (ML eq_refl). dand ML as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [intros _; split_conj; try lia_std; unfold ctable_live; cbn; cbv [N_CODES]; split_conj; try reflexivity; try lia_std; exact TOK |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

(* [comment removed for export] *)
Lemma sinv_ll_bad : forall cx st lf cf cf' rv,
  sinv cx st lf cf -> t_mode st = LENLENS -> 0 <= rv < 18446744073709551616 ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_ct st BAD rv 7 0 (t_shave st)) lf cf' /\ meas cx (st_ct st BAD rv 7 0 (t_shave st)) < meas cx st.
Proof.
  intros cx st lf cf cf' rv (R & W & P & Mo) Hm Hrv Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb0 db ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_ct, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

(* [comment removed for export] *)
Lemma sinv_tb : forall cx st lf cf ci H1 B1 ncode nlen ndist,
  sinv cx st lf cf -> t_mode st = TABLE ->
  t_cin st <= ci -> ci <= c_n cx -> 14 <= B1 -> B1 <= 40 -> 0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci ->
  8 * (c_n cx - ci) + B1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  4 <= ncode -> ncode <= 19 -> 257 <= nlen -> nlen <= 286 -> 1 <= ndist -> ndist <= 30 ->
  sinv cx (st_tb st LENLENS ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist 0) lf cf /\
  meas cx (st_tb st LENLENS ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist 0) < meas cx st.
Proof.
  intros cx st lf cf ci H1 B1 ncode nlen ndist (R & W & P & Mo) Hm H1c H2 H3 H4 H5 H6 H7 H8 N1 N2 N3 N4 N5 N6.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode0 nlen0 ndist0 shave nx whave wnext].
  unfold sinv, st_tb, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (TABLE = HEAD \/ TABLE = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  pose proof (hold_shr_bound H1 B1 14 ltac:(lia_std) ltac:(lia_std)) as Hs.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1c H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [intros _; split_conj; try lia_std; intros j0 Hj0; exfalso; lia_std |].
    split_conj; mode_vacuous.
  - clear - H8 H3. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.
(* [comment removed for export] *)
Lemma sinv_tb_bad : forall cx st lf cf ci H1 B1 ncode nlen ndist,
  sinv cx st lf cf -> t_mode st = TABLE ->
  t_cin st <= ci -> ci <= c_n cx -> 14 <= B1 -> B1 <= 40 -> 0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci ->
  8 * (c_n cx - ci) + B1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= ncode -> ncode < 4294967296 -> 0 <= nlen -> nlen < 4294967296 -> 0 <= ndist -> ndist < 4294967296 ->
  sinv cx (bad_of (st_tb st TABLE ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist (t_shave st))) lf cf /\
  meas cx (bad_of (st_tb st TABLE ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist (t_shave st))) < meas cx st.
Proof.
  intros cx st lf cf ci H1 B1 ncode nlen ndist (R & W & P & Mo) Hm H1c H2 H3 H4 H5 H6 H7 H8 N1 N2 N3 N4 N5 N6.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode0 nlen0 ndist0 shave nx whave wnext].
  unfold sinv, st_tb, bad_of, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (TABLE = HEAD \/ TABLE = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  pose proof (hold_shr_bound H1 B1 14 ltac:(lia_std) ltac:(lia_std)) as Hs.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1c H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear - H8 H3. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FXG.
Local Ltac st_cell_tac Hp1 Hp2 :=
  lazymatch goal with
  | |- mem_u32 _ (wbytes _ (w64 ?a) _) ?a _ => apply mem_u32_stored; clear - Hp1 Hp2; lia_std
  | |- mem_u64 _ (wbytes _ (w64 ?a) _) ?a _ => apply mem_u64_stored; clear - Hp1 Hp2; lia_std
  | |- mem_u32 _ (wbytes _ _ _) _ _ => apply mem_u32_frame; [st_cell_tac Hp1 Hp2 | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std]
  | |- mem_u64 _ (wbytes _ _ _) _ _ => apply mem_u64_frame; [st_cell_tac Hp1 Hp2 | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std]
  | |- _ => assumption
  end.
Local Ltac st_rest_set_tac :=
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_sh, st_ct, st_lt, st_tb in *; icx_cbn;
  pose proof two64_eq as TW64;
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17);
  repeat split; st_cell_tac Hp1 Hp2.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
Lemma st_rest_set140 : forall cx st M v,
  st_rest R_segs cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest R_segs cx (st_sh st v) (wbytes M (w64 (c_p cx + 156)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
(* [comment removed for export] *)
Lemma st_rest_llt : forall cx st M v,
  st_rest R_segs cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest R_segs cx (st_lt st v 0)
    (* a worker 1.4: the distcode store (p+128) comes between lencode and lenbits *)
    (wbytes (wbytes (wbytes (wbytes M (w64 (c_p cx + 120)) (Z_to_le_bytes 8 (c_p cx + 1384)))
                            (w64 (c_p cx + 128)) (Z_to_le_bytes 8 (c_p cx + 1384)))
                    (w64 (c_p cx + 136)) (Z_to_le_bytes 4 v))
            (w64 (c_p cx + 160)) (Z_to_le_bytes 8 (c_p cx + 1384))).
Proof.
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_lt in *; icx_cbn. cbv [cp_addr o_codes]. icx_cbn.
  pose proof two64_eq as TW64.
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  rewrite Z.mul_0_r, Z.add_0_r.
  repeat split; st_cell_tac Hp1 Hp2.
Qed.

(* [comment removed for export] *)
Lemma st_rest_tb3 : forall cx st M vc vn vd,
  st_rest R_segs cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest R_segs cx (st_tb st (t_mode st) (t_cin st) (t_hold st) (t_bits st) vc vn vd (t_shave st))
    (wbytes (wbytes (wbytes M (w64 (c_p cx + 144)) (Z_to_le_bytes 4 vc))
                    (w64 (c_p cx + 148)) (Z_to_le_bytes 4 vn))
            (w64 (c_p cx + 152)) (Z_to_le_bytes 4 vd)).
Proof.
  intros cx st M vc vn vd H Hp1 Hp2; destruct cx, st; unfold st_rest, st_tb in *; icx_cbn.
  pose proof two64_eq as TW64.
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; st_cell_tac Hp1 Hp2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PL (cx : ictx) (fin : Z -> Z) (M0 : mem) (st : ist) (cf : Z -> Z) (j : Z) (M : mem) : Prop :=
  s_std cx fin M /\ st_at R_segs cx (st_sh st j) M /\ s_ret cx st M /\ s_out cx st M /\
  mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf /\ mpostL R_segs M0 M (fp_loop cx).

Lemma PL_store140 : forall cx fin M0 st cf jo M a v,
  ctx_ok ROMHI_S cx -> PL cx fin M0 st cf jo M -> a = c_p cx + 156 -> 0 <= v < 4294967296 ->
  PL cx fin M0 st cf v (wbytes M (w64 a) (Z_to_le_bytes 4 v)).
Proof.
  intros cx fin M0 st cf jo M a v CX H -> Hv.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & [Hmode SREST] & RET & OUT & HC & HP0). open_std STD. unfold PL. icx_cbn. cbv [N_LENS N_CODES] in *.
  cbv [ROMHI_S] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (st_rest_set140 _ _ _ v SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1. clear SREST.
  unfold st_sh in SR1, Hmode |- *. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1, Hmode |- *.
  zmem_transport M (p + 156) (Z_to_le_bytes 4 v).
  split_conj; try assumption; try close_std; try exact HAG; try exact I. split; assumption.
Qed.

Lemma PL_store_lens : forall cx fin M0 st cf jo M a v,
  ctx_ok ROMHI_S cx -> PL cx fin M0 st cf jo M -> c_p cx + 168 <= a -> a + 2 <= c_p cx + 808 ->
  PL cx fin M0 st cf jo (wbytes M (w64 a) (Z_to_le_bytes 2 v)).
Proof.
  intros cx fin M0 st cf jo M a v CX H Ha1 Ha2.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & SAT & RET & OUT & HC & HP0). open_std STD. unfold PL. icx_cbn. cbv [N_LENS N_CODES] in *.
  cbv [ROMHI_S] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zmem_transport M a (Z_to_le_bytes 2 v).
  split_conj; try assumption; try close_std; try exact HAG; try exact I.
Qed.

Lemma PL_intro : forall cx fin M0 st lf cf M,
  k_mem cx fin M0 st lf cf M -> PL cx fin M0 st cf (t_shave st) M /\ mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf.
Proof.
  intros cx fin M0 st lf cf M H. open_kmem H. split; [| exact Hlens]. unfold PL. destruct st. split_conj; assumption.
Qed.
Lemma PL_kmem : forall cx fin M0 st lf cf j M,
  PL cx fin M0 st cf j M -> mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> k_mem cx fin M0 (st_sh st j) lf cf M.
Proof.
  intros cx fin M0 st lf cf j M (A & B & C & C2 & D & E) HL. unfold k_mem. destruct st. split_conj; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TABLE_CODE.
Hypothesis ITABLE : itable_spec_s.
Hypothesis CLHEAD : clhead_stmt.

(* [comment removed for export] *)
Definition s_regs_llt (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -240 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kRA = c_p cx + 168 /\ zget_l Rb l kS6 = 16209 /\
  zget_l Rb l kT5 = JTAB_ADDR /\
  s_vars cx st Rb l /\ zget_l Rb l kS11 = c_q cx + t_cin st.

(* [comment removed for export] *)
Lemma ll_table_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_shave st = 19 -> sinv cx st lf cf ->
  s_regs_llt cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LL_TABLE (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). rewrite Hsh in ML. dand ML as (_ & _ & _ & Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hlf7). clear MODE_.
  assert (L7 : forall i, 0 <= i < 19 -> lf i <= 7).
  { apply order_covers. intros j0 Hj0. rewrite order_f_model by exact Hj0. apply Hlf7. exact Hj0. }
  clear Hlf7.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode shave. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  unfold s_regs_llt, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (i_frame_slots _ _ FRM) as FS. icx_cbn. cbv [JTAB_ADDR] in FS.
  dand FS as (S16 & S32 & S8 & S24 & S96 & S104 & S88 & S0 & S152 & S136).
  prune_rng.
  zkeysb. unfold L_LL_TABLE, L_LL_RET, L_TBLERR, L_CL_HEAD, L_RELOAD_A1, L_ITABLE in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (st_rest_llt _ _ _ 7 SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1.
  unfold st_lt in SR1. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1.
  clear SREST Hmode.
  (* a worker 1.4: FOUR stores here: lencode (p+120), distcode (p+128, new in 1.4), lenbits (p+136), next (p+160) *)
  zstep Rfd.                          (* sd a1,120(s0) *)
  zstep Rfd.                          (* sd a1,128(s0): 1.4 *)
  zstep Rfd.                          (* sw a0,136(s0) *)
  zstep Rfd.                          (* sd a1,160(s0) *)
  rename SR1 into SREST.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    destruct (work_arr Mx p Wp ltac:(lia) ltac:(rewrite TW64; lia)) as (wf & Hwork & Rwf);
    dand (rom_it_tabs Mx ROM) as (RT1 & RT2 & RT3 & RT4) end.
  lazymatch goal with H120 : mem_u32 _ ?Mx (p + 136) 7, H144 : mem_u64 _ ?Mx (p + 160) (p + 1384) |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    rename H120 into C120n; rename H144 into C144n end.
  unfold itable_spec_s, itable_spec_at in ITABLE.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ITABLE Rx lx Mx MD T CODES p 0 19 0 7 (p + 136) (u + -240) 88560 zc lf cf wf Hh) end.
  all: first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => cbv [cty o_lens o_next o_work o_lenbits]; zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- _ \/ _ => left; cbv [o_lenbits]; reflexivity
       | |- ZSEP _ => unfold ZSEP; pose proof (sep_p_rom _ _ SEP) as D; cbn [c_p] in D; cbv [STATE_SIZE ROM_LO_ALL DEXT_ADDR] in D |- *; clear - D; lia
       | |- _ mod 16 = 0 => first [ exact (proj1 (proj2 AL)) | apply mod0_add; [lia | exact (proj1 AL) | reflexivity] ]
       | |- mem_wr _ _ _ _ => first [ assumption | cbv [FR_IT]; eapply mem_wr_sub; [exact Wstk | lia | lia] ]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => first [ assumption | eapply mem_u64_eqv; [| exact C144n]; cbv [o_codes]; lia ]
       | |- mem_u32 _ _ _ _ => assumption
       | |- forall i : Z, _ -> _ <= _ < _ => assumption
       | |- _ = CODES -> _ => intros _; split; [lia | split; [reflexivity | intros s Hs; replace (0 + s) with s by lia; apply L7; lia]]
       | |- _ = DISTS -> _ => intros X; discriminate X
       | |- forall s : Z, _ -> _ <= 15 => intros s Hs; replace (0 + s) with s by lia; pose proof (L7 s Hs); lia
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE N_LENS N_CODES FR_IT DEXT_ADDR]; cbn [it_room]; first [assumption | lia]
       end | match goal with |- ?G => idtac "ITFAIL" G end ].
  (* [comment removed for export] *)
  intros R' M' cf' wf' Hrv Hret3 Hcf' Hwf' Rcf' Rwf' HP Hlens' Hcodes' Hwork' Hnext' Hbits' KE.
  (* [comment removed for export] *)
  pose proof (tab_ok_of_itable CODES lf cf wf cf' 0 19 0 7) as BR0.
  pose proof (it_fail_shape CODES (arr_init N_LENS lf) 0 19 (arr_init N_CODES cf) 0 7 (arr_init N_WORK wf)) as FS0.
  set (r := inflate_table CODES (arr_init N_LENS lf) 0 19 (arr_init N_CODES cf) 0 7 (arr_init N_WORK wf)) in *.
  clearbody r. cbv zeta in BR0, FS0.
  assert (BR : it_ret r = 0 ->
     tab_ok CODES (rdc cf' (CDyn 0)) (it_bits r) (it_table r - 0) = true /\ 1 <= it_bits r <= 15 /\
     0 + 2 ^ it_bits r <= it_table r <= 0 + it_room CODES /\ (forall i, 0 <= i < N_CODES -> ~ (0 <= i < it_table r) -> cf' i = cf i)).
  { intros Hrz. apply BR0; cbv [N_LENS N_CODES]; cbn [it_room]; try assumption; try lia.
    - intros s Hs. replace (0 + s) with s by lia. pose proof (L7 s Hs). lia.
    - intros _. split; [lia | split; [reflexivity | intros s Hs; replace (0 + s) with s by lia; apply L7; lia]]. }
  assert (FS : it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 7) by (intros Hnz; exact (FS0 Hnz)).
  clear BR0 FS0.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hwork RT1 RT2 RT3 RT4 C120n C144n Hcodes.
  (* [comment removed for export] *)
  unfold st_rest in SREST. icx_cbn. cbv [cp_addr o_codes] in SREST. icx_cbn.
  dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & _ & C124 & C128 & C132 & C136 & C140 & _).
  unfold it_fp in HP. cbv [o_next o_work o_codes N_WORK N_CODES FR_IT] in HP. zreattachL HP.
  cbv [N_CODES] in Rcf', BR. cbn [it_room] in BR. cbv [o_next o_codes] in Hnext'.
  destruct (Z.eq_dec (it_ret r) 0) as [Hr0 | Hnz].
  - (* [comment removed for export] *)
    dand (BR Hr0) as (TOK & Hb15 & Htab & Hout). clear BR FS.
    rewrite Hr0 in Hrv. rewrite Z.sub_0_r in TOK.
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    clear C140.
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* U-only: ld t5,104(sp) *)
    pose proof (sinv_ll_ct _ _ lf cf cf' (it_bits r) (it_table r) SI0 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) TOK ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLHEAD (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (st_ct (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist 19 nx whave wnext)
                       CODELENS 0 (it_bits r) (it_table r) 0)
                lf cf' CX0 Hh Hfin eq_refl SI1) end.
    + unfold s_regs_cl, s_fix, s_vars, st_ct; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    + unfold k_mem, st_at, st_rest, s_ret, st_ct; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [CODELENS]; assumption | exact HAG | exact I | eapply mem_u64_eqv; [| eassumption]; lia ].
    + eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
  - (* [comment removed for export] *)
    destruct (FS Hnz) as [Ht0 Hb7]. clear BR FS.
    assert (Hrm : exists rm, it_ret r mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r mod 18446744073709551616). split; [reflexivity|].
      destruct Hret3 as [E | [E | E]]; [exfalso; exact (Hnz E) | rewrite E | rewrite E]; clear;
        [ change (1 mod 18446744073709551616) with 1 | change ((-1) mod 18446744073709551616) with 18446744073709551615 ]; lia_std. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with H : mem_u64 _ ?Mx (u + -160) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      apply mem_u64_mod in H; rewrite Hrm in H end.
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (sinv_ll_bad _ _ lf cf cf' rm SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1)) ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    ist_cbn. rewrite Ht0 in Hnext'. rewrite Hb7 in Hbits'.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRA1 Rx Mx _ lf cf' SI1 ME1) end.
    + unfold s_regs_reload, st_ct; icx_cbn; zkeys; split_conj; try zreg; try (intros C; discriminate C).
    + unfold k_mem, st_at, st_rest, s_ret, st_ct; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | exact I | eapply mem_u64_eqv; [| eassumption]; lia ].
Qed.

(* [comment removed for export] *)
Lemma ll_fill_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_ncode st <= t_shave st -> sinv cx st lf cf ->
  s_regs_llt cx st Rb l -> zget_l Rb l kA5 = t_shave st -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LL_FILL (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI RG La5 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  destruct (PL_intro _ _ _ _ _ _ _ KM) as [HP HlensX]. open_kmem KM. open_std STD. clear SAT SRET SOUT HlensX.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _ & _ & _ & _ & Hlf7). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  unfold s_regs_llt, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (rom_order_arr _ ROM) as Hord.
  prune_rng.
  zkeysb. unfold L_LL_FILL, L_LL_TABLE, L_LL_FLOOP, L_LL_FEND, A_ORDER in *. pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z_lt_dec 18 shave) as [H19 | H18].
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_table_s _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI0) end.
    + unfold s_regs_llt, s_vars; icx_cbn; zkeys; split_conj; zreg.
    + apply (PL_kmem _ _ _ _ lf cf shave) in HP; [exact HP | exact Hlens].
    + exact KA0.
  - zbr Rfd false.
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (2 * shave) ltac:(rewrite shiftl_1m; reflexivity).
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd. zlit.                  (* [comment removed for export] *)
    zstep Rfd. zlit.                  (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fill_loop 19 (fun (_ : Z) Mq => PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                 (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf shave Mq)
                Rx lx Mx MD T p shave shave lf Hh) end;
      try zreg; try assumption; try lia.
    + unfold ZSEP. exact (sep_p_rom _ _ SEP).
    + intros i Hi. rewrite order_f_model by lia. apply Hlf7. lia.
    + intros M' jo' a v HP' Ha1 Ha2. eapply PL_store_lens; [exact CX0 | exact HP' | cbn; lia | cbn; lia].
    + (* [comment removed for export] *)
      intros R' M' lf' Ha2 Wp' Hord' Hlens' Rlf' Hlf7' HP' HKC. cbv [keptc KS_LF] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LL_FEND in *.
      clear Hlens Hord Hin Wp Wstk Wob Ww ROM FRM CST HK Hcodes HP.
      pose proof (fun M' jo a v => PL_store140 (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                    (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    cf jo M' a v CX0) as HPa.
      tstoreP Rfd HP' HPa.            (* [comment removed for export] *)
      pose proof (sinv_ll _ _ lf cf cin hold bits 19 lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' Hlf7') as [SI1 ME1].
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (ll_table_s _ fin MD T M0 Rx lx Mx
                  (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cin hold bits 19)
                  lf' cf CX0 Hh Hfin eq_refl eq_refl SI1) end.
      * unfold s_regs_llt, s_vars, st_ll; icx_cbn; zkeys; split_conj; try zreg; keptc_trans.
      * apply (PL_kmem _ _ _ _ lf' cf 19) in HP'; [exact HP' | exact Hlens'].
      * eapply KALL_mono; [| exact KA0]. exact ME1.
Qed.

(* [comment removed for export] *)
Lemma ll_setup_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_shave st < t_ncode st -> sinv cx st lf cf ->
  s_fix cx Rb l -> s_vars cx st Rb l -> zget_l Rb l kS11 = c_q cx + t_cin st ->
  zget_l Rb l kA5 = t_shave st -> zget_l Rb l kA2 = t_ncode st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LL_SETUP (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI FX VR L10 La5 La2 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. open_K K.
  destruct (PL_intro _ _ _ _ _ _ _ KM) as [HP HlensX]. open_kmem KM. open_std STD. clear SAT SRET SOUT HlensX.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _ & _ & _ & _ & Hlf7). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  unfold s_fix in FX. unfold s_vars in VR. icx_cbn. destr_conj FX. destr_conj VR.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (rom_order_arr _ ROM) as Hord.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  prune_rng.
  zkeysb. unfold L_LL_SETUP, L_LL_HEAD, L_LL_FILL0, L_LL_FILL, L_LEAVE_LD, A_ORDER in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd. zext32.                  (* [comment removed for export] *)
  zstep Rfd. zext32.                  (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 * shave) ltac:(symmetry; apply zext32_shift31; lia).
  zstep Rfd. zlit.                    (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (fun M' jo a v => PL_store140 (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cf jo M' a v CX0) as HPa.
  pose proof (fun M' jo a v => PL_store_lens (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cf jo M' a v CX0) as HPb.
  cbn [c_p] in HPa, HPb.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (lenlens_loop 19 (fun jo Mq => PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
               (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf jo Mq)
              Rx lx Mx MD T p q n ncode shave cin bits hold fin lf Hh) end;
    try zreg; try assumption; try lia.
  - unfold ZSEP. exact (sep_p_q _ _ SEP).
  - unfold ZSEP. exact (sep_p_rom _ _ SEP).
  - intros i Hi. rewrite order_f_model by lia. apply Hlf7. lia.
  - (* [comment removed for export] *)
    intros R' M' j' B' H' lf' G9 G24 G25 G27 X1 X2 X3 X4 X5 X6 X7 X8 Wp' Hin' Hord' Hlens' Rlf' Hlf7' HP' HKC.
    cbv [keptc KS_LL] in HKC. destr_conj HKC. zimps. zkeys.
    pose proof (sinv_ll _ _ lf cf n H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' ltac:(exact Hlf7')) as [SI1 ME1].
    pose proof (PL_kmem _ _ _ _ lf' cf j' _ HP' Hlens') as KM'. dand KM' as (STD' & SAT' & SRET' & SOUT' & HL' & HC' & HP0').
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KLL Rx Mx (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) n H' B' j') lf' cf SI1) end.
    + unfold s_regs_leave_ld, st_ll; icx_cbn; zkeys; split_conj; try zreg; try assumption. all: try (rewrite G25; lia).
    + exact STD'.
    + exact SAT'.
    + exact SRET'.
    + exact SOUT'.
    + exact HL'.
    + exact HC'.
    + exact HP0'.
  - (* [comment removed for export] *)
    intros R' M' ci' B' H' lf' G9 G24 G25 G27 G13 G26 G2 X1 X2 X3 X4 X5 X6 X7 X8 Wp' Hin' Hord' Hlens' Rlf' Hlf7' HP' HKC.
    cbv [keptc KS_LL] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LL_FILL0, L_LL_FILL in *.
    pose proof (sinv_ll _ _ lf cf ci' H' B' ncode lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' ltac:(exact Hlf7')) as [SI1 ME1].
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_fill_s _ fin MD T M0 Rx lx Mx
                (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' ncode)
                lf' cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end.
    + unfold s_regs_llt, s_vars, st_ll; icx_cbn; zkeys; split_conj; try zreg; try assumption.
    + unfold st_ll; cbn [t_shave]; zreg.
    + apply (PL_kmem _ _ _ _ lf' cf ncode) in HP'; [exact HP' | exact Hlens'].
    + eapply KALL_mono; [| exact KA0]. exact ME1.
Qed.

Theorem arm_LENLENS_s0 : arm_stmt L_LENLENS LENLENS.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  assert (C128 : mem_u32 R_segs M (p + 144) ncode) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  assert (C140 : mem_u32 R_segs M (p + 156) shave) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  clear SREST Hmode STD SRET SOUT Hlens Hcodes HP0.
  zkeysb. unfold L_LENLENS, L_LL_SETUP, L_LL_FILL in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  destruct (Z_lt_dec shave ncode) as [Hlt | Hge].
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_setup_s _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI) end;
      [ unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg
      | unfold s_vars; icx_cbn; zkeys; split_conj; zreg
      | (icx_cbn; zkeys; zreg) .. | exact KM0 | exact K ].
  - zbr Rfd false.
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_fill_s _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI) end;
      [ unfold s_regs_llt, s_vars; icx_cbn; zkeys; split_conj; zreg
      | icx_cbn; zkeys; zreg | exact KM0 | exact K ].
Qed.

(* [comment removed for export] *)
Ltac zval k :=
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?l) _ _) _ =>
    let o := eval cbn [alookup Pos.eqb] in (alookup l k) in
    lazymatch o with Some ?v => v end
  end.

(* [comment removed for export] *)
Lemma table_body : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = TABLE -> sinv cx st lf cf ->
  s_fix cx Rb l ->
  zget_l Rb l kS9 = c_n cx - cin1 -> zget_l Rb l kS4 = c_ob cx + t_cout st -> zget_l Rb l kS3 = c_osz cx - t_cout st ->
  zget_l Rb l kS8 = hold1 -> zget_l Rb l kS1 = bits1 -> zget_l Rb l kS7 = t_out st ->
  zget_l Rb l kS11 = c_q cx + cin1 -> zget_l Rb l kS10 = c_q cx + cin1 ->
  t_cin st <= cin1 -> cin1 <= c_n cx -> 14 <= bits1 -> bits1 <= 40 -> 0 <= hold1 -> hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_TAB_BODY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX Hh Hfin Hm SI FX L25 L20 L19 L24 L9 L7o L27 L28
         Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. open_K K.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  unfold s_fix in FX. icx_cbn. destr_conj FX.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  prune_rng.
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_TAB_BODY, L_LL_SETUP, L_BAD_TAB, L_BADMSG_S11 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (hold1 mod 32) ltac:(symmetry; apply land31_mod; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (hold1 / 2 ^ 14) ltac:(rewrite (Z.mod_small hold1) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg ((hold1 / 32) mod 32) ltac:(symmetry; apply bits_54_59; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg ((hold1 / 1024) mod 16) ltac:(symmetry; apply bits_50_60; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (mod_range hold1 32 ltac:(lia)) as R1. pose proof (mod_range (hold1 / 32) 32 ltac:(lia)) as R2.
  pose proof (mod_range (hold1 / 1024) 16 ltac:(lia)) as R3.
  pose proof (hold_shr_bound hold1 bits1 14 ltac:(lia) ltac:(lia)) as R4.
  (* [comment removed for export] *)
  let vc := zval 13%positive in let vn := zval 16%positive in let vd := zval 17%positive in
  pose proof (st_rest_tb3 _ _ _ vc vn vd SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1.
  unfold st_tb in SR1. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1.
  clear SREST.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  rename SR1 into SREST.
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (JB : forall RJ,
    zget RJ kSP = u + -240 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA0 = u -> zget RJ kA1 = 0 -> zget RJ kRA = p + 168 -> zget RJ kT6 = -16180 ->
    zget RJ kT4 = 30 -> zget RJ kT5 = 67008 -> zget RJ kS6 = 16209 ->
    zget RJ kS9 = n - cin1 -> zget RJ kS4 = ob + cout -> zget RJ kS3 = osz - cout ->
    zget RJ kS10 = q + cin1 -> zget RJ kS8 = hold1 / 2 ^ 14 -> zget RJ kS1 = bits1 - 14 -> zget RJ kS7 = out ->
    realizes R_segs (zcfg R_segs 89316 (zupd RJ []) Mc MD) T) end.
  { intros RJ. intros. zkeys.
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (sinv_tb_bad _ _ lf cf cin1 hold1 bits1 ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1)
                  SI0 eq_refl Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI1 ME1].
    ist_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KB11 Rx Mx _ lf cf SI1 ME1) end.
    - unfold s_regs_disp, s_fix, s_vars, st_tb; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - zreg.
    - unfold k_mem, st_at, st_tb, s_ret; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: first [cbv [TABLE]; assumption | exact HAG | exact I]. }
  destruct (Z_lt_dec 29 (hold1 mod 32)) as [Hn1 | Hn1].
  { zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => apply (JB Rx) end; zreg. }
  zbr Rfd false.
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z_lt_dec ((hold1 / 32) mod 32) 30) as [Hn2 | Hn2].
  2: { zbr Rfd true.                  (* [comment removed for export] *)
       lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => apply (JB Rx) end; zreg. }
  zbr Rfd false.
  clear JB.
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  clear Hmode.
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (st_rest_set140 _ _ _ 0 SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1.
  unfold st_sh in SR1. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1.
  clear SREST.
  zstep Rfd.                          (* [comment removed for export] *)
  rename SR1 into SREST.
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (sinv_tb _ _ lf cf cin1 hold1 bits1 ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1)
                SI0 eq_refl Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI1 ME1].
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ll_setup_s _ fin MD T M0 Rx lx Mx
              (st_tb (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                     LENLENS cin1 (hold1 / 2 ^ 14) (bits1 - 14) ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1) 0)
              lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end.
  - unfold s_fix, st_tb; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold s_vars, st_tb; icx_cbn; zkeys; split_conj; zreg.
  - unfold st_tb; icx_cbn; zkeys; zreg.
  - unfold st_tb; icx_cbn; zkeys; zreg.
  - unfold st_tb; icx_cbn; zkeys; zreg.
  - unfold k_mem, st_at, st_tb, s_ret; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LENLENS]; assumption | exact HAG | exact I].
  - eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
Qed.

Theorem arm_TABLE_s0 : arm_stmt L_TABLE TABLE.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof KM as KM0. pose proof K as KA0. open_K K. open_kmem KM. open_std STD.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  clear SAT SRET SOUT Hlens Hcodes ROM Wstk Wp Wob Ww FRM CST HK.
  prune_rng.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_TABLE, L_TAB_LOOP, L_TAB_BODY, L_TAB_SKIP, L_LEAVE_LD in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z_lt_dec 13 bits) as [Hb14 | Hb14].
  - zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (table_body _ fin MD T M0 Rx lx Mx
                (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 Hh Hfin eq_refl SI) end;
      [ unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg
      | (icx_cbn; zkeys; first [zreg | lia]) .. | exact KM0 | exact KA0 ].
  - zbr Rfd false.
    zstep Rfd.                        (* [comment removed for export] *)
    assert (Hkk : exists k : nat, 14 - 8 * Z.of_nat k <= bits < 22 - 8 * Z.of_nat k /\ (1 <= k <= 2)%nat).
    { destruct (Z_lt_dec bits 6); [exists 2%nat | exists 1%nat]; cbn; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (table_loop k Rx lx Mx MD T q n cin hold bits fin Hh Hfin Hk1 Hk2) end;
      [ lia | lia | lia | lia | lia | lia | lia | zreg .. | exact Hin | | ].
    + (* [comment removed for export] *)
      intros R' hold' j' G27 G25 G24 G9 Hj' Hh' Hkn HKC. cbv [keptc KS_TB] in HKC. destr_conj HKC. zimps. zkeys.
      pose proof (sinv_pull _ _ lf cf n hold' j' SI ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 _].
      dand KM0 as (STD' & SAT' & SRET' & SOUT' & HL' & HC' & HP0').
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx (st_pull (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) n hold' j') lf cf SI1) end;
        [ unfold s_regs_leave_ld, st_pull; icx_cbn; zkeys; split_conj; try zreg; try assumption; rewrite G25; lia
        | exact STD' | exact SAT' | exact SRET' | exact SOUT' | exact HL' | exact HC' | exact HP0' ].
    + (* [comment removed for export] *)
      intros R' hold' j' G28 G27 G25 G24 G9 Hj' Hh' Hkn HKC. cbv [keptc KS_TB] in HKC. destr_conj HKC. zimps. zkeys.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (table_body _ fin MD T M0 Rx [] Mx
                  (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf (cin + Z.of_nat k) hold' j' CX0 Hh Hfin eq_refl SI) end;
        [ unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; try zreg; assumption
        | (icx_cbn; zkeys; first [zreg | assumption | lia]) .. | exact KM0 | exact KA0 ].
Qed.
End TABLE_CODE.

(* [comment removed for export] *)
End FXG.
End S_Table.

Module S_CodelensT.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ItCovIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.ItBridge.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_LenL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF S_ClDefs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_LENS_RET : Z := 89276.   (* [comment removed for export] *)
Definition L_DTAB : Z := 89792.       (* [comment removed for export] *)
Definition L_DISTS_RET : Z := 89848.  (* [comment removed for export] *)
Definition L_TBLERR : Z := 89864.     (* [comment removed for export] *)
Definition L_CL_OK : Z := 91832.      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_u64_eqv : forall M a v v', v = v' -> mem_u64 R_segs M a v -> mem_u64 R_segs M a v'.
Proof. intros M a v v' <- H. exact H. Qed.
Lemma mem_u64_mod : forall M a v, mem_u64 R_segs M a v -> mem_u64 R_segs M a (v mod 18446744073709551616).
Proof. intros M a v H. unfold mem_u64 in *. change 18446744073709551616 with two64. rewrite Z_to_le_bytes_mod by lia_std. exact H. Qed.

(* [comment removed for export] *)
Lemma le_cell2_range : forall bs i, 0 <= le_cell 2 bs i < 65536.
Proof.
  intros bs i. unfold le_cell.
  set (l := firstn (Z.to_nat 2) (skipn (Z.to_nat (2 * i)) bs)).
  pose proof (bytes_le_to_Z_bound l) as R. pose proof (bytes_le_to_Z_nonneg l) as R0.
  assert (L : (length l <= 2)%nat) by (subst l; rewrite length_firstn; cbn; lia_std).
  assert (P : 2 ^ (8 * Z.of_nat (length l)) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia_std).
  change (2 ^ 16) with 65536 in P. lia_std.
Qed.
Lemma work_arr : forall M p, mem_wr R_segs M p 7176 -> 0 <= p -> p + 7176 <= two64 ->
  exists wf, mem_arr 2 R_segs M (p + 808) 288 wf /\ (forall i, 0 <= i < 288 -> 0 <= wf i < 65536).
Proof.
  intros M p W Hp1 Hp2.
  destruct (mem_wr_readable R_segs wr_rd_R M (p + 808) 576 ltac:(eapply mem_wr_sub; [exact W | lia_std | lia_std]) ltac:(lia_std)) as [bs [A B]].
  exists (le_cell 2 bs). split.
  - apply (mem_arr_of_bytes R_segs 2 M (p + 808) 288 bs A); try lia_std.
  - intros i _. apply le_cell2_range.
Qed.

(* [comment removed for export] *)
Lemma rom_it_tabs : forall M, rom_ok M ->
  mem_arr 2 R_segs M LBASE_ADDR 31 (arr_get lbase_a) /\ mem_arr 2 R_segs M LEXT_ADDR 31 (arr_get lext_a) /\
  mem_arr 2 R_segs M DBASE_ADDR 32 (arr_get dbase_a) /\ mem_arr 2 R_segs M DEXT_ADDR 32 (arr_get dext_a).
Proof.
  intros M H. cbv [LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR]. split_conj.
  - eapply mem_arr_ext; [apply rom_lbase_arr; exact H | intros; apply lbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_lext_arr; exact H | intros; apply lext_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dbase_arr; exact H | intros; apply dbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dext_arr; exact H | intros; apply dext_f_model; assumption].
Qed.

(* [comment removed for export] *)
Lemma i_frame_slots : forall cx M, i_frame cx M ->
  mem_u64 R_segs M (c_u cx + -216) (c_p cx + 1384) /\ mem_u64 R_segs M (c_u cx + -200) (c_p cx + 160) /\
  mem_u64 R_segs M (c_u cx + -224) (c_p cx + 136) /\ mem_u64 R_segs M (c_u cx + -208) (c_p cx + 808) /\
  mem_u64 R_segs M (c_u cx + -120) (c_u cx) /\ mem_u64 R_segs M (c_u cx + -128) 0 /\
  mem_u64 R_segs M (c_u cx + -144) (-16180) /\ mem_u64 R_segs M (c_u cx + -232) (c_p cx + 140) /\
  mem_u64 R_segs M (c_u cx + -152) (c_p cx + 168) /\ mem_u64 R_segs M (c_u cx + -136) JTAB_ADDR.
Proof. intros cx M H. unfold i_frame in H. destr_conj H. split_conj; assumption. Qed.

End FXG.
Ltac ist_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma rng_dc : forall cx st lf cf, sinv cx st lf cf -> match t_dc st with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end.
Proof. intros cx st lf cf (R & _). unfold RNG in R. destr_conj R. assumption. Qed.

Lemma pow2_pos : forall b, 0 <= b -> 0 < 2 ^ b.
Proof. intros b Hb. apply Z.pow_pos_nonneg; lia_std. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_tab (st : ist) (m rv lb : Z) (dc : codeptr) (db nx : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) rv
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) dc lb db
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) nx (t_whave st) (t_wnext st).

(* [comment removed for export] *)
Lemma sinv_cl_bad : forall cx st lf cf cf' rv lb dc db nx,
  sinv cx st lf cf -> t_mode st = CODELENS -> 0 <= rv < 18446744073709551616 ->
  0 <= lb < 4294967296 -> 0 <= db < 4294967296 ->
  match dc with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end -> 0 <= nx -> nx <= N_CODES ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_tab st BAD rv lb dc db nx) lf cf' /\ meas cx (st_tab st BAD rv lb dc db nx) < meas cx st.
Proof.
  intros cx st lf cf cf' rv lb dc db nx (R & W & P & Mo) Hm Hrv Hlb Hdb Hdc Hnx1 Hnx2 Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc0 lb0 db0 ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_tab, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]] |].
  - clear W P Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear W P. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

(* [comment removed for export] *)
Lemma sinv_cl_len_ : forall cx st lf cf cf' lb o2 db nx,
  sinv cx st lf cf -> t_mode st = CODELENS ->
  1 <= lb -> lb <= 15 -> 1 <= db -> db <= 15 -> 0 <= o2 -> o2 <= nx -> nx <= N_CODES ->
  tab_ok LENS (rdc cf' (CDyn 0)) lb o2 = true -> tab_ok DISTS (rdc cf' (CDyn o2)) db (nx - o2) = true ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_tab st LEN_ 0 lb (CDyn o2) db nx) lf cf' /\ meas cx (st_tab st LEN_ 0 lb (CDyn o2) db nx) < meas cx st.
Proof.
  intros cx st lf cf cf' lb o2 db nx (R & W & P & Mo) Hm Hlb1 Hlb2 Hdb1 Hdb2 Ho1 Ho2 Hnx TL TD Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc0 lb0 db0 ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_tab, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]] |].
  - clear W P Mf TL TD. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear W P. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [mode_vacuous |].
    split; [intros _; unfold tables_live; cbn [t_lc t_dc t_lb t_db t_nx]; cbv [N_CODES]; split_conj; try reflexivity; try assumption; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CLT.
Hypothesis ITABLE : itable_spec_s.
Hypothesis IFAST : ifast_spec_s.

(* [comment removed for export] *)
Lemma lenu_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN_ -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LEN_ (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof (sinv_len_ cx st lf cf SI Hmd) as [SI1 ME1].
  open_kmem KM. destruct SAT as [Hmode SREST].
  dand RG as (FIX & VARS & G27).
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold s_fix, s_vars in FIX, VARS. icx_cbn. destr_conj FIX. destr_conj VARS.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold st_le in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
  zkeysb. unfold L_LEN_, L_LEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.                          (* [comment removed for export] *)
  clear Hmode.
  tstep1 Rfd.                         (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_s IFAST _ fin MD T M0 Rx lx Mx
              (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end.
  - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LEN]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG | exact I].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.

(* [comment removed for export] *)
Local Ltac itable_pre SEP AL Wstk LF15 :=
  first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => cbv [cty o_lens o_next o_work o_lenbits o_distbits]; zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- _ \/ _ => first [ left; cbv [o_lenbits]; reflexivity | right; cbv [o_distbits]; reflexivity ]
       | |- ZSEP _ => unfold ZSEP; pose proof (sep_p_rom _ _ SEP) as D; cbn [c_p] in D; cbv [STATE_SIZE ROM_LO_ALL DEXT_ADDR ROMHI_S] in D |- *; clear - D; lia
       | |- _ mod 16 = 0 => first [ exact (proj1 (proj2 AL)) | apply mod0_add; [lia | exact (proj1 AL) | reflexivity] ]
       | |- mem_wr _ _ _ _ => first [ assumption | cbv [FR_IT]; eapply mem_wr_sub; [exact Wstk | lia | lia] ]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => first [ assumption | eapply mem_u64_eqv; [| eassumption]; cbv [o_codes]; lia ]
       | |- mem_u32 _ _ _ _ => assumption
       | |- forall i : Z, _ -> _ <= _ < _ => assumption
       | |- _ = CODES -> _ => intros X; discriminate X
       | |- _ = DISTS -> _ => first [ intros X; discriminate X | intros _; lia ]
       | |- forall s : Z, _ -> _ <= 15 => intros s Hs; first [ replace (0 + s) with s by lia | idtac ]; apply LF15; lia
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE N_LENS N_CODES FR_IT ENOUGH_LENS ENOUGH_DISTS DEXT_ADDR]; cbn [it_room]; cbv [ENOUGH_LENS ENOUGH_DISTS]; first [assumption | lia]
       end | match goal with |- ?G => idtac "ITFAIL" G end ].

(* [comment removed for export] *)
Theorem cldone_s : cldone_stmt.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hhave SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (MC : t_mode st = CODELENS -> 257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            t_shave st <= t_nlen st + t_ndist st /\ (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) by mode_get MODE_.
  specialize (MC Hm). dand MC as (Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hsh & Hlf15 & _). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  assert (LF15 : forall i, 0 <= i < nlen + ndist -> lf i <= 15) by (intros i Hi; apply Hlf15; lia). clear Hlf15 Hsh Hhave.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  pose proof (rng_dc _ _ _ _ SI0) as Hdc. cbn [t_dc] in Hdc. cbv [N_CODES] in Hdc.
  unfold s_regs_cld, s_fix, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (i_frame_slots _ _ FRM) as FS. icx_cbn. cbv [JTAB_ADDR] in FS.
  dand FS as (S16 & S32 & S8 & S24 & S96 & S104 & S88 & S0 & S152 & S136).   (* [comment removed for export] *)
  unfold st_rest in SREST. icx_cbn.
  dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn. clear SRET.
  assert (Rdb : 0 <= db < 4294967296) by lia. pose proof (Rlf 256 ltac:(lia)) as R256.
  prune_rng.
  zkeysb. unfold L_CL_DONE, L_LENS_RET, L_DTAB, L_DISTS_RET, L_TBLERR, L_CL_OK, L_BADMSG_S10, L_RELOAD_A1, L_ITABLE, L_LEN_ in *.
  cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.                         (* [comment removed for export] *)
  destruct (Z.eq_dec (lf 256) 0) as [Hz | Hnz].
  { (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
    cbn [t_mode] in MB. change (rank CODELENS) with 20 in MB.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB10 Rx Mx (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf
                (sinv_bad_of _ _ _ _ SI0)) end.
    - clear - MB. lia.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - lazymatch goal with |- 0 <= ?x < _ => assert (EA2 : x = 66659) by zreg; rewrite EA2 end. lia.
    - unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std.
      all: first [exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | exact I]. }
  (* [comment removed for export] *)
  zbr Rfd false.                      (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    destruct (work_arr Mx p Wp ltac:(lia) ltac:(rewrite TW64; lia)) as (wf & Hwork & Rwf);
    dand (rom_it_tabs Mx ROM) as (RT1 & RT2 & RT3 & RT4) end.
  lazymatch goal with H120 : mem_u32 _ ?Mx (p + 136) 9, H144 : mem_u64 _ ?Mx (p + 160) (p + 1384) |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    rename H120 into C120n; rename H144 into C144n end.
  pose proof ITABLE as ITABLE1. unfold itable_spec_s, itable_spec_at in ITABLE1.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ITABLE1 Rx lx Mx MD T LENS p 0 nlen 0 9 (p + 136) (u + -240) 89276 zc lf cf wf Hh) end.
  all: itable_pre SEP AL Wstk LF15.
  clear ITABLE1.
  (* [comment removed for export] *)
  intros R' M' cf' wf' Hrv Hret3 Hcf' Hwf' Rcf' Rwf' HP Hlens' Hcodes' Hwork' Hnext' Hbits' KE.
  set (r := inflate_table _ _ _ _ _ _ _ _) in *.
  assert (BR : it_ret r = 0 ->
     tab_ok LENS (rdc cf' (CDyn 0)) (it_bits r) (it_table r - 0) = true /\ 1 <= it_bits r <= 15 /\
     0 + 2 ^ it_bits r <= it_table r <= 0 + it_room LENS /\ (forall i, 0 <= i < N_CODES -> ~ (0 <= i < it_table r) -> cf' i = cf i)).
  { intros Hr0. apply (tab_ok_of_itable LENS lf cf wf cf' 0 nlen 0 9); cbv [N_LENS N_CODES]; cbn [it_room]; cbv [ENOUGH_LENS]; try assumption; try lia.
    - intros s Hs. replace (0 + s) with s by lia. apply LF15. lia.
    - intros X; discriminate X.
    - intros X; discriminate X. }
  assert (FS1 : it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 9).
  { intros Hne. exact (inflate_table_fail_shape LENS (arr_init N_LENS lf) 0 nlen (arr_init N_CODES cf) 0 9 (arr_init N_WORK wf) Hne). }
  clearbody r.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hwork RT1 RT2 RT3 RT4 C120n C144n Hcodes Hlens.
  unfold it_fp in HP. cbv [o_next o_work o_codes o_lenbits N_WORK N_CODES FR_IT] in HP. zreattachL HP.
  cbv [o_lens o_codes o_work o_next o_lenbits N_LENS N_CODES N_WORK] in Hlens', Hcodes', Hwork', Hnext', Hbits'.
  cbv [N_CODES] in Rcf', BR. cbv [N_WORK] in Rwf'. cbn [it_room] in BR. cbv [ENOUGH_LENS] in BR.
  destruct (Z.eq_dec (it_ret r) 0) as [Hr0 | Hnz1].
  2: { (* [comment removed for export] *)
    destruct (FS1 Hnz1) as [Ht0 Hb9]. clear BR FS1.
    assert (Hrm : exists rm, it_ret r mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r mod 18446744073709551616). split; [reflexivity|].
      destruct Hret3 as [E | [E | E]]; [exfalso; exact (Hnz1 E) | rewrite E | rewrite E];
        [ rewrite Z.mod_small by lia_std; lia_std
        | replace ((-1) mod 18446744073709551616) with 18446744073709551615 by reflexivity; lia_std ]. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with H : mem_u64 _ ?Mx (u + -160) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      apply mem_u64_mod in H; rewrite Hrm in H end.
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (sinv_cl_bad _ _ lf cf cf' rm (it_bits r) dc db (it_table r) SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1))
                  ltac:(lia) ltac:(lia) Hdc ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    rewrite Ht0 in *. rewrite Hb9 in *.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRA1 Rx Mx _ lf cf' SI1 ME1) end.
    + unfold s_regs_reload; icx_cbn; zkeys; split_conj; try zreg. all: intros C; discriminate C.
    + unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | exact I | eapply mem_u64_eqv; [| eassumption]; lia ]. }
  (* [comment removed for export] *)
  dand (BR Hr0) as (TOK1 & Hb15 & Htab1 & Hout1). clear BR FS1.
  rewrite Hr0 in Hrv. rewrite Z.sub_0_r in TOK1.
  pose proof (pow2_pos (it_bits r) ltac:(lia)) as Hpw1.
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 * nlen) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2; rewrite ?Z.mod_small by lia; lia).
  zstep Rfd.                          (* U-only: ld a0,88(sp), the lens pointer *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    dand (rom_it_tabs Mx ROM) as (RT1 & RT2 & RT3 & RT4) end.
  lazymatch goal with H124 : mem_u32 _ ?Mx (p + 140) 6, H112 : mem_u64 _ ?Mx (p + 128) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    rename H124 into C124n; rename H112 into C112n end.
  pose proof ITABLE as ITABLE2. unfold itable_spec_s, itable_spec_at in ITABLE2.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ITABLE2 Rx lx Mx MD T DISTS p nlen ndist (it_table r) 6 (p + 140) (u + -240) 89848 zc lf cf' wf' Hh) end.
  all: itable_pre SEP AL Wstk LF15.
  clear ITABLE2.
  (* [comment removed for export] *)
  intros R'' M'' cf'' wf'' Hrv2 Hret32 Hcf'' Hwf'' Rcf'' Rwf'' HP2 Hlens'' Hcodes'' Hwork'' Hnext'' Hbits'' KE2.
  set (r2 := inflate_table _ _ _ _ _ _ _ _) in *.
  assert (BR2 : it_ret r2 = 0 ->
     tab_ok DISTS (rdc cf'' (CDyn (it_table r))) (it_bits r2) (it_table r2 - it_table r) = true /\ 1 <= it_bits r2 <= 15 /\
     it_table r + 2 ^ it_bits r2 <= it_table r2 <= it_table r + it_room DISTS /\
     (forall i, 0 <= i < N_CODES -> ~ (it_table r <= i < it_table r2) -> cf'' i = cf' i)).
  { intros Hr0'. apply (tab_ok_of_itable DISTS lf cf' wf' cf'' nlen ndist (it_table r) 6); cbv [N_LENS N_CODES]; cbn [it_room]; cbv [ENOUGH_DISTS]; try assumption; try lia.
    - intros s Hs. apply LF15. lia.
    - intros X; discriminate X. }
  assert (FS2 : it_ret r2 <> 0 -> it_table r2 = it_table r /\ it_bits r2 = 6).
  { intros Hne. exact (inflate_table_fail_shape DISTS (arr_init N_LENS lf) nlen ndist (arr_init N_CODES cf') (it_table r) 6 (arr_init N_WORK wf') Hne). }
  clearbody r2.
  unfold kept_eq in KE2. zkeys. destr_conj KE2. zimps.
  clear RT1 RT2 RT3 RT4 C124n Hcodes' Hlens' Hwork' Hnext'.
  unfold it_fp in HP2. cbv [o_next o_work o_codes o_distbits N_WORK N_CODES FR_IT] in HP2. zreattachL HP2.
  cbv [o_lens o_codes o_work o_next o_distbits N_LENS N_CODES N_WORK] in Hlens'', Hcodes'', Hwork'', Hnext'', Hbits''.
  cbv [N_CODES] in Rcf'', BR2. cbn [it_room] in BR2. cbv [ENOUGH_DISTS] in BR2.
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z.eq_dec (it_ret r2) 0) as [Hr20 | Hnz2].
  - (* [comment removed for export] *)
    dand (BR2 Hr20) as (TOK2 & Hb25 & Htab2 & Hout2). clear BR2 FS2.
    rewrite Hr20 in *.
    pose proof (pow2_pos (it_bits r2) ltac:(lia)) as Hpw2.
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd. zlit.                  (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* U-only: ld t5,104(sp) *)
    zbr Rfd false.                    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (TOK1' : tab_ok LENS (rdc cf'' (CDyn 0)) (it_bits r) (it_table r) = true).
    { eapply tab_ok_ext_rd; [| exact TOK1]. intros i Hi. unfold rdc. apply Hout2; cbv [N_CODES]; lia. }
    pose proof (sinv_cl_len_ _ _ lf cf cf'' (it_bits r) (it_table r) (it_bits r2) (it_table r2) SI0 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia)
                  TOK1' TOK2 ltac:(cbv [N_CODES]; exact Rcf'')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (lenu_s (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (IST LEN_ last flags cin cout hold bits out 0 length offset extra (CDyn 0) (CDyn (it_table r)) (it_bits r) (it_bits r2)
                     ncode nlen ndist shave (it_table r2) whave wnext)
                lf cf'' CX0 Hh Hfin eq_refl SI1) end.
    + unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    + unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [LEN_]; assumption | exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | exact I | eapply mem_u64_eqv; [| eassumption]; lia ].
    + eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
  - (* [comment removed for export] *)
    destruct (FS2 Hnz2) as [Ht2 Hb6]. clear BR2 FS2.
    assert (Hrm : exists rm, it_ret r2 mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r2 mod 18446744073709551616). split; [reflexivity|].
      destruct Hret32 as [E | [E | E]]; [exfalso; exact (Hnz2 E) | rewrite E | rewrite E];
        [ rewrite Z.mod_small by lia_std; lia_std
        | replace ((-1) mod 18446744073709551616) with 18446744073709551615 by reflexivity; lia_std ]. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    lazymatch goal with H : mem_u64 _ ?Mx (u + -160) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      apply mem_u64_mod in H; rewrite Hrm in H end.
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd. zstep Rfd. zlit.       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (sinv_cl_bad _ _ lf cf cf'' rm (it_bits r) (CDyn (it_table r)) (it_bits r2) (it_table r2) SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1))
                  ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(cbv [N_CODES]; exact Rcf'')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    rewrite Ht2 in *. rewrite Hb6 in *.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRA1 Rx Mx _ lf cf'' SI1 ME1) end.
    + unfold s_regs_reload; icx_cbn; zkeys; split_conj; try zreg. all: intros C; discriminate C.
    + unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | exact I | eapply mem_u64_eqv; [| eassumption]; lia ].
Qed.

End CLT.
End FXG.
End S_CodelensT.

Module S_CodelensL.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_CL_LOOP : Z := 88668.   (* [comment removed for export] *)
Definition L_CL_DLOOP : Z := 88704.  (* [comment removed for export] *)
Definition L_CL_RES : Z := 88788.    (* [comment removed for export] *)
Definition L_CL_P17 : Z := 88872.    (* [comment removed for export] *)
Definition L_CL_X17 : Z := 89044.    (* [comment removed for export] *)
Definition L_CL_P16 : Z := 88932.    (* [comment removed for export] *)
Definition L_CL_X16 : Z := 89080.    (* [comment removed for export] *)
Definition L_CL_P18 : Z := 88992.    (* [comment removed for export] *)
Definition L_CL_X18 : Z := 89140.    (* [comment removed for export] *)
Definition L_CL_CHK : Z := 89168.    (* [comment removed for export] *)
Definition L_CL_FILL : Z := 89180.   (* [comment removed for export] *)
Definition L_CL_FILLX : Z := 89204.  (* [comment removed for export] *)
Definition L_CL_NEXT : Z := 89212.   (* [comment removed for export] *)
Definition L_LVX_CL : Z := 93560.    (* [comment removed for export] *)
Definition L_LEAVE_A7 : Z := 93656.  (* [comment removed for export] *)
Definition L_BADREP0 : Z := 93492.   (* [comment removed for export] *)
Definition L_BADREP : Z := 93408.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ctab_bits : forall cf lb nx i,
  tab_ok CODES (rdc cf (CDyn 0)) lb nx = true -> 0 <= i < 2 ^ lb -> 1 <= code_bits (cf i) <= lb /\ 2 ^ lb <= nx.
Proof.
  intros cf lb nx i T Hi. pose proof (tab_root_entry CODES (rdc cf (CDyn 0)) lb nx i T Hi) as (X & _ & Y & _).
  unfold rdc in X. rewrite Z.add_0_l in X. split; [exact X | exact Y].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zext32_shift31 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) (31 mod 64) = 2 * x.
Proof.
  intros x Hx. change (31 mod 64) with 31. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma land3_range : forall x, 0 <= Z.land x 3 < 4.
Proof. intros. apply land_ones_range with (k := 2). lia_std. Qed.
Lemma land7_range' : forall x, 0 <= Z.land x 7 < 8.
Proof. intros. apply land_ones_range with (k := 3). lia_std. Qed.
Lemma land127_range : forall x, 0 <= Z.land x 127 < 128.
Proof. intros. apply land_ones_range with (k := 7). lia_std. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KS_CP : list positive := [2; 3; 4; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 30; 31; 32]%positive.
(* [comment removed for export] *)
Definition KS_CD : list positive := [2; 3; 4; 5; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 27; 32]%positive.
(* [comment removed for export] *)
Definition KS_CF : list positive := [2; 3; 4; 5; 7; 8; 9; 10; 11; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32]%positive.
(* [comment removed for export] *)
Definition KS_CX : list positive := [2; 3; 4; 5; 6; 8; 9; 11; 12; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31; 32]%positive.
End FXG.
Ltac keptc_closeC := cbv [keptc KS_CP KS_CD KS_CF KS_CX]; split_conj; try exact I; zreg.
Ltac keptc_chainC HK := cbv [keptc KS_CP KS_CD KS_CF KS_CX] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_pull : forall (N : nat) (pc pcx : Z) Rb l M MD T (q n need c0 b0 ci B H : Z) (fin : Z -> Z),
  ((pc = L_CL_P17 /\ pcx = L_CL_X17) \/ (pc = L_CL_P16 /\ pcx = L_CL_X16) \/ (pc = L_CL_P18 /\ pcx = L_CL_X18)) ->
  m_halted MD = None ->
  zget_l Rb l kS9 = n - ci -> zget_l Rb l kS11 = q + ci -> zget_l Rb l kT2 = B -> zget_l Rb l kA7 = B ->
  zget_l Rb l kT1 = need -> zget_l Rb l kS8 = H ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < need -> need <= 22 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  (* [comment removed for export] *)
  (forall R' (H' : Z),
     zget R' kS8 = H' -> zget R' kS9 = 0 -> zget R' kS11 = q + n -> zget R' kA7 = b0 + 8 * (n - c0) ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) < need -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_CP ->
     realizes R_segs (zcfg R_segs L_LEAVE_A7 (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' (ci' B' H' : Z),
     zget R' kS9 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS10 = q + ci' -> zget R' kA7 = B' -> zget R' kT2 = B' -> zget R' kS8 = H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> need <= B' -> B' <= 29 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_CP ->
     realizes R_segs (zcfg R_segs pcx (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs pc (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros pc pcx Rb l M MD T q n need c0 b0 ci B H fin Hpc Hh Ls8 Ls10 Lt2 La7 Lt1 Ls7
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt Hneed HH1 HH2 HBc Hq1 Hn26 Hq2 Hin Rfin KX KD; [lia|].
  zkeys. unfold L_CL_P17, L_CL_X17, L_CL_P16, L_CL_X16, L_CL_P18, L_CL_X18, L_LEAVE_A7 in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB. pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]]; (
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz];
    [ zbr Rfd false; zstep Rfd;
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia;
      [ replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_closeC ]
    | zbr Rfd true;
      pose proof (Rfin ci ltac:(lia)) as Rb1;
      tld1 Hin ci Rfin;                 (* [comment removed for export] *)
      tstep1 Rfd;                       (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia);
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]; rewrite pow2_add8 in Hp1 by lia;
      zstep Rfd;                        (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      zsetreg (H + fin ci * 2 ^ B) ltac:(lia);
      assert (HH' : 0 <= H + fin ci * 2 ^ B < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia);
      zstep Rfd;                        (* [comment removed for export] *)
      zstep Rfd;                        (* [comment removed for export] *)
      destruct (Z_lt_dec (B + 8) need) as [Hmore | Hdone];
      [ zbr Rfd true;
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx ?MDx) ?Tx =>
          eapply (IH _ _ Rx lx Mx MDx Tx q n need c0 b0 (ci + 1) (B + 8) (H + fin ci * 2 ^ B) fin) end;
        [ first [left; split; reflexivity | right; left; split; reflexivity | right; right; split; reflexivity] | ..];
        try zreg; try lia; try eassumption;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HK; eapply KD; try eassumption; try lia; keptc_chainC HK
      | zbr Rfd false;
        zstep Rfd;                      (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (H + fin ci * 2 ^ B)) end;
        try zreg; try lia; keptc_closeC ] ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_decode : forall (N : nat) Rb l M MD T (u p q n lb lm nx c0 b0 ci B H : Z) (fin cf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -240 -> zget_l Rb l kA5 = p + 1384 -> zget_l Rb l kA6 = lm ->
  zget_l Rb l kT5 = q + ci -> zget_l Rb l kS11 = q + ci -> zget_l Rb l kS9 = n - ci ->
  zget_l Rb l kT4 = B -> zget_l Rb l kA7 = B -> zget_l Rb l kS8 = H ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < code_bits (cf (Z.land lm H)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  p + 8200 <= u -> u + 208 <= 140737488355328 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 R_segs M (p + 1384) 1444 cf -> mem_u64 R_segs M (u + -136) 67008 ->
  (* [comment removed for export] *)
  (forall R' (H' : Z),
     zget R' kS8 = H' -> zget R' kS9 = 0 ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 22 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_CD ->
     realizes R_segs (zcfg R_segs L_LVX_CL (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' (ci' B' H' : Z),
     zget R' kS11 = q + ci' -> zget R' kS9 = n - ci' -> zget R' kA7 = B' -> zget R' kS8 = H' ->
     zget R' kT0 = code_bits (cf (Z.land lm H')) -> zget R' kT3 = Z.land lm H' -> zget R' kT4 = 30 -> zget R' kT5 = 67008 ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits (cf (Z.land lm H')) <= B' -> B' <= 22 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_CD ->
     realizes R_segs (zcfg R_segs L_CL_RES (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_CL_DLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T u p q n lb lm nx c0 b0 ci B H fin cf Hh Lsp La5 La6 Lt5 Ls10 Ls8 Lt4 La7 Ls7
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Hq1 Hn26 Hq2 Hp1 Hp2 Hu1 Hu2 Hin Rfin Hcodes Hjt KX KD; [lia|].
  zkeys. unfold L_CL_DLOOP, L_CL_RES, L_LVX_CL in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  assert (HB14 : B <= 14) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    all: first [replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_closeC]. }
  zbr Rfd true.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.                   (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1']. rewrite pow2_add8 in Hp1' by lia.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1'.
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (land_mask_l H' lb ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (ctab_bits cf lb nx (Z.land lm H') TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits1 _].
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * Z.land lm H') ltac:(symmetry; apply shiftl_2).
  zstep Rfd.                          (* [comment removed for export] *)
  tld4_bits Hcodes (Z.land lm H').    (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (code_bits (cf (Z.land lm H')))) as [Hmore | Hdone].
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T u p q n lb lm nx c0 b0 (ci + 1) (B + 8) H' fin cf Hh) end;
      try zreg; try lia; try eassumption.
    intros R' ci' B' H'' G27 G25 G18 G24 G6 G29 G30 G31 X1 X2 X3 X4 X5 X6 X7 X8 HK.
    eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chainC HK.
  - zbr Rfd false.
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zstep Rfd.                        (* U-only: ld t5,104(sp) *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_closeC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stub_CL : forall Rb l M MD T (q n c0 b0 u rv : Z),
  m_halted MD = None ->
  zget_l Rb l kT1 = n - c0 -> zget_l Rb l kT2 = q + c0 -> zget_l Rb l kS1 = b0 -> zget_l Rb l kSP = u + -240 ->
  0 <= n - c0 -> n - c0 < 4294967296 -> mem_u64 R_segs M (u + -160) rv ->
  (forall R', zget R' kS1 = b0 + 8 * (n - c0) -> zget R' kS11 = q + n -> zget R' kS2 = rv ->
     keptc Rb l R' KS_CX -> realizes R_segs (zcfg R_segs L_LEAVE (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_LVX_CL (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T q n c0 b0 u rv Hh Lt1 Lt2 Ls0 Lsp H1 H2 Hrv K.
  zkeys. unfold L_LVX_CL, L_LEAVE in *.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (8 * (n - c0)) ltac:(symmetry; apply shiftl_3).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd. zext32.                  (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* U-only: the jump to L_LEAVE after the reload of s2 *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg. keptc_closeC.
Qed.

(* [comment removed for export] *)
End FXG.
Ltac zside1c := first [reflexivity | exact I | zlia].
Ltac tstore_arrPc fd Ha i HP HPres :=
  lazymatch type of Ha with
  | mem_arr ?k ?segs ?M ?base ?n ?f =>
      let pc := zpc in
      fd pc ltac:(fun F E D =>
        lazymatch type of D with
        | decode_any _ = Some (Store SZ1 _ _ _, _) =>
            eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ2 _ _ _, _) =>
            eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ4 _ _ _, _) =>
            eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        end);
      lazymatch goal with
      | |- realizes _ (zcfg _ _ _ (wbytes M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
          apply (mem_arr_upd segs k M base n f a i v) in Ha; [| zlia | zlia];
          (let kn := eval cbv in (Z.to_nat k) in change (Z.to_nat k) with kn in Ha);
          (let HP' := fresh in pose proof (HPres M a v HP ltac:(zside1c) ltac:(zside1c)) as HP'; clear HP; rename HP' into HP);
          repeat match goal with
          | H : mem_arr ?k' segs M ?base' ?n' ?f' |- _ =>
              first [ apply (mem_arr_frame segs k' M base' n' f' a (Z_to_le_bytes kk v)) in H; [|unfold zdisj; zlen_norm; zlia]
                    | idtac "tstore_arrPc: mem_arr fact dropped at array store" a; clear H ]
          end;
          zmem_post
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
(* [comment removed for export] *)
End FXG.
Ltac tstorePc fd HP HPres :=
  let pc := zpc in
  fd pc ltac:(fun F E D =>
    lazymatch type of D with
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply zu_sd; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    end);
  lazymatch goal with
  | |- realizes _ (zcfg _ _ _ (wbytes ?M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
      (let HP' := fresh in pose proof (HPres M a v HP ltac:(zside1c) ltac:(zside1c)) as HP'; clear HP; rename HP' into HP);
      zmem_post_arr; zmem_post
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_fill : forall (N : nat) (P : mem -> Prop) Rb l M MD T (u p q n j je len : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA3 = j -> zget_l Rb l kA7 = je -> zget_l Rb l kT1 = len -> zget_l Rb l kRA = p + 168 ->
  je - j <= Z.of_nat N -> 0 <= j -> j < je -> je <= 320 -> 0 <= len -> len < 65536 ->
  0 < p -> p + 7176 <= 140737488355328 -> 1 <= q -> 0 <= n -> q + n <= 140737488355328 -> p + 8200 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr R_segs M p 7176 ->
  mem_arr 1 R_segs M q n fin -> mem_arr 4 R_segs M (p + 1384) 1444 cf -> mem_arr 2 R_segs M (p + 168) 320 lf ->
  P M ->
  (forall M' (a v : Z), P M' -> p + 168 <= a -> a + 2 <= p + 808 -> P (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (lf' : Z -> Z),
     zget R' kA3 = je ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> P M' ->
     (forall i, 0 <= i < 320 -> j <= i < je -> lf' i = len) ->
     (forall i, 0 <= i < 320 -> ~ (j <= i < je) -> lf' i = lf i) ->
     keptc Rb l R' KS_CF ->
     realizes R_segs (zcfg R_segs L_CL_FILLX (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_CL_FILL (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p q n j je len fin cf lf Hh La3 La7 Lt1 Lra
    HN Hj0 Hj1 Hje Hl0 Hl1 Hp1 Hp2 Hq1 Hn0 Hq2 Hu1 Hu2 SPQ Wp Hin Hcodes Hlens HP HPb KD; [lia|].
  zkeys. unfold L_CL_FILL, L_CL_FILLX in *. pose proof two64_eq as TW64.
  zstep Rfd.                          (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 * j) ltac:(symmetry; apply zext32_shift31; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  tstore_arrPc Rfd Hlens j HP HPb.    (* [comment removed for export] *)
  destruct (Z.eq_dec (j + 1) je) as [Hlast | Hmore].
  - zbr Rfd false.                    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KD Rx Mx (zfupd lf j len)) end;
      try zreg; try eassumption.
    all: first [ intros i Hi Hij; unfold zfupd; destruct (Z.eqb_spec i j); first [reflexivity | lia] | keptc_closeC ].
  - zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T u p q n (j + 1) je len fin cf _ Hh) end;
      try zreg; try lia; try eassumption.
    intros R' M' lf' G14 W' Hin' Hcodes' Hlens' HP' Hin_ Hout_ HK.
    eapply (KD R' M' lf'); try eassumption.
    all: first [ intros i Hi Hij;
                 first [ destruct (Z.eq_dec i j) as [-> | Hne];
                         [ rewrite Hout_ by lia; unfold zfupd; rewrite Z.eqb_refl; reflexivity | apply Hin_; lia ]
                       | rewrite Hout_ by lia; unfold zfupd; destruct (Z.eqb_spec i j); [lia | reflexivity] ]
               | keptc_chainC HK ].
Qed.
End FXG.
End S_CodelensL.

Module S_Codelens.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S.S_LenF.S_DistL S_TableL S_Table S_ClDefs S_CodelensL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
Definition KS_CR : list positive := [2; 3; 4; 5; 9; 11; 12; 13; 15; 16; 17; 19; 20; 21; 22; 23; 24; 32]%positive.   (* [comment removed for export] *)
End FXG.
Ltac keptc_closeR := cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX]; split_conj; try exact I; zreg.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
(* [comment removed for export] *)
End FXG.
Ltac kopen HK := cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX] in HK; destr_conj HK; zimps.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
(* [comment removed for export] *)
End FXG.
Ltac keptc_transC :=
  repeat match goal with H : keptc _ _ _ _ |- _ => cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX] in H; destr_conj H end;
  cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX]; split_conj; try exact I;
  rewrite ?zget_zupd in *; cbv [zget_l] in *; cbn [alookup Pos.eqb] in *;
  first [ assumption | reflexivity
        | etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
(* [comment removed for export] *)
End FXG.
Ltac kgoal := first [ zreg | assumption | OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK.ITac.zarith_goal; lia | etransitivity; [eassumption | solve [lia | symmetry; assumption]] | keptc_transC ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_res : forall (P : Z -> mem -> Prop) Rb l M MD T (u p q n nlen nd lb lm nx c0 b0 j ci B H : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -240 -> zget_l Rb l kS0 = p -> zget_l Rb l kRA = p + 168 ->
  zget_l Rb l kA2 = nlen -> zget_l Rb l kA4 = nd -> zget_l Rb l kA5 = p + 1384 -> zget_l Rb l kA6 = lm ->
  zget_l Rb l kA3 = j -> zget_l Rb l kS11 = q + ci -> zget_l Rb l kS9 = n - ci -> zget_l Rb l kA7 = B ->
  zget_l Rb l kS1 = b0 -> zget_l Rb l kS8 = H ->
  zget_l Rb l kT0 = code_bits (cf (Z.land lm H)) -> zget_l Rb l kT3 = Z.land lm H ->
  zget_l Rb l kT4 = 30 -> zget_l Rb l kT5 = 67008 ->
  0 <= j -> j < nd -> nd <= 316 -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  code_bits (cf (Z.land lm H)) <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> (forall i, 0 <= i < j -> lf i <= 15) ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 -> p + 8200 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr R_segs M p 7176 -> mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 R_segs M (p + 1384) 1444 cf -> mem_arr 2 R_segs M (p + 168) 320 lf ->
  P j M ->
  (forall M' (a v : Z), P j M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' (jo a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (* [comment removed for export] *)
  (forall R' (ci' B' H' : Z),
     zget R' kS8 = H' -> zget R' kS9 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kA7 = B' -> zget R' kS1 = b0 ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ci) + B ->
     keptc Rb l R' KS_CR ->
     realizes R_segs (zcfg R_segs L_LEAVE_A7 (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall (pc : Z) R' (ci' B' H' : Z),
     (pc = L_BADREP0 \/ pc = L_BADREP) ->
     zget R' kS8 = H' -> zget R' kS9 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS10 = q + ci' -> zget R' kS1 = B' ->
     zget R' kT4 = 30 -> zget R' kT5 = 67008 ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ci) + B ->
     keptc Rb l R' KS_CR ->
     realizes R_segs (zcfg R_segs pc (zupd R' []) M MD) T) ->
  (* [comment removed for export] *)
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kA3 = j' -> zget R' kS8 = H' -> zget R' kS9 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS1 = B' ->
     zget R' kT4 = 30 -> zget R' kT5 = 67008 ->
     j < j' -> j' <= nd -> ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' + 1 <= 8 * (n - ci) + B ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes R_segs (zcfg R_segs L_CL_NEXT (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_CL_RES (zupd Rb l) M MD) T.
Proof.
  intros P Rb l M MD T u p q n nlen nd lb lm nx c0 b0 j ci B H fin cf lf Hh
    Lsp Ls9 Lra La2 La4 La5 La6 La3 Ls10 Ls8 La7 Ls0 Ls7 Lt0 Lt3 Lt4 Lt5
    Hj0 Hj1 Hnd Hc0 Hc1 Hc2 Hb0 HB Hbe HB40 HH1 HH2 HBc Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rlf Hlf15
    Hq1 Hn0 Hn26 Hq2 Hp1 Hp2 Hpu Hu2 SPQ Wp Hin Rfin Hcodes Hlens HP HPa HPb KX KB KN.
  zkeys. unfold L_CL_RES, L_CL_NEXT, L_LEAVE_A7, L_BADREP0, L_BADREP, L_CL_P17, L_CL_X17, L_CL_P16, L_CL_X16, L_CL_P18, L_CL_X18,
    L_CL_CHK, L_CL_FILL, L_CL_FILLX in *.
  pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  set (e := cf (Z.land lm H)) in *.
  pose proof (code_bits_range e) as Rbe. pose proof (code_val_range e) as Rve.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * Z.land lm H) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.                          (* [comment removed for export] *)
  tld4_val Hcodes (Z.land lm H).      (* [comment removed for export] *)
  fold e.
  zstep Rfd.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CHK : forall RC (ci' B' H' copy len : Z),
    zget RC kA7 = copy -> zget RC kT1 = len -> zget RC kS8 = H' -> zget RC kS1 = B' ->
    zget RC kS9 = n - ci' -> zget RC kS11 = q + ci' -> zget RC kS10 = q + ci' -> zget RC kA3 = j ->
    zget RC kT4 = 30 -> zget RC kT5 = 67008 -> zget RC kA4 = nd -> zget RC kS0 = p -> zget RC kRA = p + 168 ->
    3 <= copy -> copy <= 138 -> 0 <= len -> len <= 15 ->
    ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
    8 * (n - ci') + B' + 1 <= 8 * (n - ci) + B ->
    keptc Rb l RC KS_CR ->
    realizes R_segs (zcfg R_segs 89168 (zupd RC []) M MD) T).
  { intros RC ci' B' H' copy len G18 G7 G24 G9 G25 G27 G28 G14 G30 G31 G15 G26 G2 Hcp1 Hcp2 Hln1 Hln2 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK.
    zkeys.
    tstep1 Rfd.                       (* [comment removed for export] *)
    destruct (Z_lt_dec nd (copy + j)) as [Hover | Hfit].
    - zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KB 93408 Rx ci' B' H') end;
        try (right; reflexivity). all: kgoal.
    - zbr Rfd true.                   (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        pose proof (fun M1 a1 v1 => HPb M1 j a1 v1) as HPbj;
        eapply (cl_fill (Z.to_nat 138) (P j) Rx lx Mx MD T u p q n j (copy + j) len fin cf lf Hh) end;
        try zreg; try lia; try eassumption.
      intros R' M' lf' G14' Wp' Hin' Hcodes' Hlens' HP' Hfill Hkeep HK'. unfold L_CL_FILLX. zimps. kopen HK'. zkeys.
      tstorePc Rfd HP' HPa.           (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KN Rx Mx (copy + j) ci' B' H' lf') end; try eassumption.
      all: first [ intros i Hi;
                   first [ destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Rlf; lia |];
                           destruct (Z_lt_dec i (copy + j)) as [Hm|Hx]; [rewrite Hfill by lia; lia | rewrite Hkeep by lia; apply Rlf; lia]
                         | destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Hlf15; lia | rewrite Hfill by lia; lia] ]
                 | kgoal ]. }
  destruct (Z_lt_dec 15 (code_val e)) as [Hrep | Hlit].
  2: { (* [comment removed for export] *)
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (H / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    tstep1 Rfd.                       (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    tstep1 Rfd.                       (* [comment removed for export] *)
    tstorePc Rfd HP HPa.              (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    zsetreg (2 * j) ltac:(symmetry; apply zext32_shift31; lia).
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (fun M1 a1 v1 => HPb M1 (j + 1) a1 v1) as HPb1.
    tstore_arrPc Rfd Hlens j HP HPb1. (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KN Rx Mx (j + 1) ci (B - code_bits e) (H / 2 ^ code_bits e) (zfupd lf j (code_val e))) end;
      try eassumption.
    all: first [ intros i Hi; unfold zfupd; destruct (Z.eqb_spec i j); [lia | first [apply Rlf; lia | apply Hlf15; lia]]
               | kgoal ]. }
  (* [comment removed for export] *)
  zbr Rfd true.                       (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  destruct (Z.eq_dec (code_val e) 16) as [E16 | N16].
  - (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (X16 : forall RX (ci' B' H' : Z),
      zget RX kS9 = n - ci' -> zget RX kS11 = q + ci' -> zget RX kS10 = q + ci' -> zget RX kA7 = B' -> zget RX kS8 = H' ->
      zget RX kT0 = code_bits e -> zget RX kA3 = j -> zget RX kRA = p + 168 -> zget RX kT4 = 30 -> zget RX kT5 = 67008 ->
      zget RX kS0 = p -> zget RX kA4 = nd ->
      ci <= ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits e + 2 <= B' -> B' <= 40 ->
      0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
      keptc Rb l RX KS_CR ->
      realizes R_segs (zcfg R_segs 89080 (zupd RX []) M MD) T).
    { intros RX ci' B' H' G25 G27 G28 G18 G24 G6 G14 G2 G30 G31 G26 G15 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK. kopen HK. zkeys.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      zstep Rfd.                      (* [comment removed for export] *)
      zsetreg (H' / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H' B'); lia).
      pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
      pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
      set (H2 := H' / 2 ^ code_bits e) in *.
      tstep1 Rfd.                     (* [comment removed for export] *)
      destruct (Z.eq_dec j 0) as [Hj | Hj].
      + (* [comment removed for export] *)
        zbr Rfd false.                (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        pose proof (pow2_le (B' - code_bits e) B' ltac:(lia)) as HP2.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KB 93492 Rx ci' (B' - code_bits e) H2) end;
          try (left; reflexivity). all: kgoal.
      + zbr Rfd true.                 (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        zsetreg (2 * (j - 1)) ltac:(symmetry; apply zext32_shift31; lia).
        zstep Rfd.                    (* [comment removed for export] *)
        pose proof (Rlf (j - 1) ltac:(lia)) as Rlj. pose proof (Hlf15 (j - 1) ltac:(lia)) as Hlj.
        tstep Rfd.                    (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        pose proof (land3_range H2) as Hcp.
        zstep Rfd.                    (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        zsetreg (H2 / 2 ^ 2) ltac:(rewrite (Z.mod_small H2) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        pose proof (hold_shr_bound H2 (B' - code_bits e) 2 ltac:(lia) ltac:(lia)) as HS3.
        tstep1 Rfd.                   (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        pose proof (pow2_le (B' - code_bits e - 2) (B' - code_bits e) ltac:(lia)) as HP3.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
          eapply (CHK Rx ci' (B' - code_bits e - 2) (H2 / 2 ^ 2) (Z.land H2 3 + 3) (lf (j - 1))) end.
        all: kgoal. }
    destruct (Z_lt_dec B (code_bits e + 2)) as [Hneed | Hhave].
    + zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (cl_pull (S (Z.to_nat (n - ci))) 88932 89080 Rx lx Mx MD T q n (code_bits e + 2) c0 b0 ci B H fin
                  ltac:(right; left; split; reflexivity) Hh) end;
        try zreg; try lia; try eassumption.
      * intros R' H' G24 G25 G27 G18 X1 X2 X3 X4 HK. zimps. kopen HK.
        eapply (KX R' n (b0 + 8 * (n - c0)) H'). all: kgoal.
      * intros R' ci' B' H' G25 G27 G28 G18 G8 G24 X1 X2 X3 X4 X5 X6 X7 X8 HK. zimps. kopen HK.
        eapply (X16 R' ci' B' H'). all: kgoal.
    + zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X16 Rx ci B H) end. all: kgoal.
  - zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd.                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (X1718 : forall (pcx k base : Z) RX (ci' B' H' : Z),
      ((pcx = 89044 /\ k = 3 /\ base = 3) \/ (pcx = 89140 /\ k = 7 /\ base = 11)) ->
      zget RX kS9 = n - ci' -> zget RX kS11 = q + ci' -> zget RX kS10 = q + ci' -> zget RX kA7 = B' -> zget RX kS8 = H' ->
      zget RX kT0 = code_bits e -> zget RX kA3 = j -> zget RX kRA = p + 168 -> zget RX kT4 = 30 -> zget RX kT5 = 67008 ->
      zget RX kS0 = p -> zget RX kA4 = nd ->
      ci <= ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits e + k <= B' -> B' <= 40 ->
      0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
      keptc Rb l RX KS_CR ->
      realizes R_segs (zcfg R_segs pcx (zupd RX []) M MD) T).
    { intros pcx k base RX ci' B' H' Hpcx G25 G27 G28 G18 G24 G6 G14 G2 G30 G31 G26 G15 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK. kopen HK. zkeys.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      destruct Hpcx as [(-> & -> & ->) | (-> & -> & ->)].
      - zstep Rfd.                    (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        zsetreg (H' / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H' B'); lia).
        pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
        pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
        set (H2 := H' / 2 ^ code_bits e) in *.
        tstep1 Rfd.                   (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        pose proof (land7_range' H2) as Hcp.
        zstep Rfd.                    (* [comment removed for export] *)
        zsetreg (H2 / 2 ^ 3) ltac:(rewrite (Z.mod_small H2) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        pose proof (hold_shr_bound H2 (B' - code_bits e) 3 ltac:(lia) ltac:(lia)) as HS3.
        zstep Rfd.                    (* [comment removed for export] *)
        tstep1 Rfd.                   (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        pose proof (pow2_le (B' - code_bits e - 3) (B' - code_bits e) ltac:(lia)) as HP3.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
          eapply (CHK Rx ci' (B' - code_bits e - 3) (H2 / 2 ^ 3) (Z.land H2 7 + 3) 0) end.
        all: kgoal.
      - zstep Rfd.                    (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        zsetreg (H' / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H' B'); lia).
        pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
        pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
        set (H2 := H' / 2 ^ code_bits e) in *.
        tstep1 Rfd.                   (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        pose proof (land127_range H2) as Hcp.
        zstep Rfd.                    (* [comment removed for export] *)
        zsetreg (H2 / 2 ^ 7) ltac:(rewrite (Z.mod_small H2) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        pose proof (hold_shr_bound H2 (B' - code_bits e) 7 ltac:(lia) ltac:(lia)) as HS3.
        zstep Rfd.                    (* [comment removed for export] *)
        tstep1 Rfd.                   (* [comment removed for export] *)
        pose proof (pow2_le (B' - code_bits e - 7) (B' - code_bits e) ltac:(lia)) as HP3.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
          eapply (CHK Rx ci' (B' - code_bits e - 7) (H2 / 2 ^ 7) (Z.land H2 127 + 11) 0) end.
        all: kgoal. }
    destruct (Z.eq_dec (code_val e) 17) as [E17 | N17].
    + (* [comment removed for export] *)
      zbr Rfd false.                  (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      destruct (Z_lt_dec B (code_bits e + 3)) as [Hneed | Hhave].
      * zbr Rfd false.                (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (cl_pull (S (Z.to_nat (n - ci))) 88872 89044 Rx lx Mx MD T q n (code_bits e + 3) c0 b0 ci B H fin
                    ltac:(left; split; reflexivity) Hh) end;
          try zreg; try lia; try eassumption.
        -- intros R' H' G24 G25 G27 G18 X1 X2 X3 X4 HK. zimps. kopen HK.
           eapply (KX R' n (b0 + 8 * (n - c0)) H'). all: kgoal.
        -- intros R' ci' B' H' G25 G27 G28 G18 G8 G24 X1 X2 X3 X4 X5 X6 X7 X8 HK. zimps. kopen HK.
           eapply (X1718 89044 3 3 R' ci' B' H'); try (left; split_conj; reflexivity). all: kgoal.
      * zbr Rfd true.                 (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X1718 89044 3 3 Rx ci B H) end;
          try (left; split_conj; reflexivity). all: kgoal.
    + (* [comment removed for export] *)
      zbr Rfd true.                   (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      destruct (Z_lt_dec B (code_bits e + 7)) as [Hneed | Hhave].
      * zbr Rfd false.                (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (cl_pull (S (Z.to_nat (n - ci))) 88992 89140 Rx lx Mx MD T q n (code_bits e + 7) c0 b0 ci B H fin
                    ltac:(right; right; split; reflexivity) Hh) end;
          try zreg; try lia; try eassumption.
        -- intros R' H' G24 G25 G27 G18 X1 X2 X3 X4 HK. zimps. kopen HK.
           eapply (KX R' n (b0 + 8 * (n - c0)) H'). all: kgoal.
        -- intros R' ci' B' H' G25 G27 G28 G18 G8 G24 X1 X2 X3 X4 X5 X6 X7 X8 HK. zimps. kopen HK.
           eapply (X1718 89140 7 11 R' ci' B' H'); try (right; split_conj; reflexivity). all: kgoal.
      * zbr Rfd true.                 (* [comment removed for export] *)
        zstep Rfd.                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X1718 89140 7 11 Rx ci B H) end;
          try (right; split_conj; reflexivity). all: kgoal.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_loop : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T (u p q n nlen nd lb lm nx ce Be j ci B H : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -240 -> zget_l Rb l kS0 = p -> zget_l Rb l kRA = p + 168 ->
  zget_l Rb l kA2 = nlen -> zget_l Rb l kA4 = nd -> zget_l Rb l kA5 = p + 1384 -> zget_l Rb l kA6 = lm ->
  zget_l Rb l kA3 = j -> zget_l Rb l kS11 = q + ci -> zget_l Rb l kT2 = q + ci -> zget_l Rb l kS9 = n - ci -> zget_l Rb l kT1 = n - ci ->
  zget_l Rb l kS1 = B -> zget_l Rb l kS8 = H -> zget_l Rb l kT4 = 30 -> zget_l Rb l kT5 = 67008 ->
  nd - j <= Z.of_nat N -> 0 <= j -> j < nd -> nd <= 316 ->
  ce <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> 8 * (n - ci) + B <= 8 * (n - ce) + Be ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> (forall i, 0 <= i < j -> lf i <= 15) ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 -> p + 8200 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr R_segs M p 7176 -> mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 R_segs M (p + 1384) 1444 cf -> mem_arr 2 R_segs M (p + 168) 320 lf ->
  P j M -> (forall (jo : Z) (M' : mem), P jo M' -> mem_u64 R_segs M' (u + -136) 67008) ->
  (forall M' (jo a v : Z), P jo M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' (jo a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (* [comment removed for export] *)
  (forall R' M' (j' ci0 B0 H' : Z) (lf' : Z -> Z),
     zget R' kS8 = H' -> zget R' kS9 = 0 -> zget R' kT1 = n - ci0 -> zget R' kT2 = q + ci0 -> zget R' kS1 = B0 ->
     ce <= ci0 -> ci0 <= n -> 0 <= B0 -> B0 + 8 * (n - ci0) <= 40 -> 0 <= H' -> H' < 2 ^ (B0 + 8 * (n - ci0)) ->
     B0 + 8 * (n - ci0) <= 8 * n -> B0 + 8 * (n - ci0) <= 8 * (n - ce) + Be ->
     j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes R_segs (zcfg R_segs L_LVX_CL (zupd R' []) M' MD) T) ->
  (* [comment removed for export] *)
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kS8 = H' -> zget R' kS9 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kA7 = B' ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes R_segs (zcfg R_segs L_LEAVE_A7 (zupd R' []) M' MD) T) ->
  (* [comment removed for export] *)
  (forall (pc : Z) R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     (pc = L_BADREP0 \/ pc = L_BADREP) ->
     zget R' kS8 = H' -> zget R' kS9 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS10 = q + ci' -> zget R' kS1 = B' ->
     zget R' kT4 = 30 -> zget R' kT5 = 67008 ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes R_segs (zcfg R_segs pc (zupd R' []) M' MD) T) ->
  (* [comment removed for export] *)
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     zget R' kS8 = H' -> zget R' kS9 = n - ci' -> zget R' kS11 = q + ci' -> zget R' kS1 = B' -> zget R' kA3 = j' ->
     zget R' kT4 = 30 -> zget R' kT5 = 67008 ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> nd <= j' -> j' <= nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr R_segs M' p 7176 -> mem_arr 1 R_segs M' q n fin -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
     mem_arr 2 R_segs M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes R_segs (zcfg R_segs L_CL_DONE (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_CL_LOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p q n nlen nd lb lm nx ce Be j ci B H fin cf lf Hh
    Lsp Ls9 Lra La2 La4 La5 La6 La3 Ls10 Lt2 Ls8 Lt1 Ls0 Ls7 Lt4 Lt5
    HN Hj0 Hj1 Hnd Hce Hc2 HB0 HB40 HH1 HH2 HBc HW Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rlf Hlf15
    Hq1 Hn0 Hn26 Hq2 Hp1 Hp2 Hpu Hu2 SPQ Wp Hin Rfin Hcodes Hlens HP HJ HPa HPb KXD KXA KBD KDN; [lia|].
  zkeys. unfold L_CL_LOOP, L_CL_DLOOP, L_CL_RES, L_CL_NEXT, L_CL_DONE, L_LVX_CL, L_LEAVE_A7, L_BADREP0, L_BADREP in *.
  pose proof two64_eq as TW64.
  pose proof (HJ j M HP) as Hjt.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb. pose proof (pow2_48 B ltac:(lia)) as HPB.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  (* [comment removed for export] *)
  assert (RES : forall RR (ci1 B1 H1 : Z),
    zget RR kSP = u + -240 -> zget RR kS0 = p -> zget RR kRA = p + 168 ->
    zget RR kA2 = nlen -> zget RR kA4 = nd -> zget RR kA5 = p + 1384 -> zget RR kA6 = lm ->
    zget RR kA3 = j -> zget RR kS11 = q + ci1 -> zget RR kS9 = n - ci1 -> zget RR kA7 = B1 ->
    zget RR kS1 = B -> zget RR kS8 = H1 -> zget RR kT0 = code_bits (cf (Z.land lm H1)) -> zget RR kT3 = Z.land lm H1 ->
    zget RR kT4 = 30 -> zget RR kT5 = 67008 -> zget RR kT1 = n - ci -> zget RR kT2 = q + ci ->
    ci <= ci1 -> ci1 <= n -> B1 = B + 8 * (ci1 - ci) -> code_bits (cf (Z.land lm H1)) <= B1 -> B1 <= 40 ->
    0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci1 ->
    keptc Rb l RR KS_CR ->
    realizes R_segs (zcfg R_segs 88788 (zupd RR []) M MD) T).
  { intros RR ci1 B1 H1. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
    eapply (cl_res P RR [] M MD T u p q n nlen nd lb lm nx ci B j ci1 B1 H1 fin cf lf Hh);
      try (cbv [zget_l alookup]; eassumption); try eassumption; try lia.
    - intros M1 a1 v1 X1 X2 X3. exact (HPa M1 j a1 v1 X1 X2 X3).
    - (* [comment removed for export] *)
      intros R' ci' B' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (KXA R' M j ci' B' H' lf). all: kgoal.
    - (* [comment removed for export] *)
      intros pc R' ci' B' H' Hpc. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (KBD pc R' M j ci' B' H' lf Hpc). all: kgoal.
    - (* [comment removed for export] *)
      intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. unfold L_CL_NEXT. zkeys.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      zstep Rfd.                      (* [comment removed for export] *)
      zstep Rfd.                      (* [comment removed for export] *)
      destruct (Z_lt_dec j' nd) as [Hlt | Hge].
      + zbr Rfd true.                 (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (IH P Rx lx Mx MD T u p q n nlen nd lb lm nx ce Be j' ci' B' H' fin cf lf' Hh) end;
          try zreg; try lia; try eassumption.
        * intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KXD RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoal.
        * intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KXA RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoal.
        * intros pc RR9 MM9 jj9 cc9 BB9 HQ9 ll9 Hpc. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KBD pc RR9 MM9 jj9 cc9 BB9 HQ9 ll9 Hpc). all: kgoal.
        * intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KDN RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoal.
      + zbr Rfd false.                (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KDN Rx Mx j' ci' B' H' lf') end. all: kgoal. }
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (4 * Z.land lm H) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.                          (* [comment removed for export] *)
  tld4_bits Hcodes (Z.land lm H).     (* [comment removed for export] *)
  destruct (Z_lt_dec B (code_bits (cf (Z.land lm H)))) as [Hdec | Hres].
  - (* [comment removed for export] *)
    zbr Rfd false.                    (* [comment removed for export] *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (cl_decode (S (Z.to_nat (n - ci))) Rx lx Mx MD T u p q n lb lm nx ci B ci B H fin cf Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (KXD R' M j ci B H' lf). all: kgoal.
    + intros R' ci' B' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (RES R' ci' B' H'). all: kgoal.
  - zbr Rfd true.                     (* [comment removed for export] *)
    zstep Rfd. zstep Rfd. zstep Rfd. (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (RES Rx ci B H) end. all: kgoal.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_cl (st : ist) (ci H B j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_cl : forall cx st lf cf ci H B j lf',
  sinv cx st lf cf -> t_mode st = CODELENS ->
  t_cin st <= ci -> ci <= c_n cx -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= j -> j <= t_nlen st + t_ndist st ->
  (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j -> lf' i <= 15) ->
  sinv cx (st_cl st ci H B j) lf' cf /\ meas cx (st_cl st ci H B j) <= meas cx st.
Proof.
  intros cx st lf cf ci H B j lf' (R & W & P & Mo) Hm H1 H2 H3 H4 H5 H6 H7 H8 Hj0 Hj1 Rlf' Hlf'.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_cl, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. cbv [N_LENS N_CODES] in R. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (MC : CODELENS = CODELENS -> 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\ shave <= nlen + ndist /\
            (forall i, 0 <= i < shave -> lf i <= 15) /\
            ctable_live (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  specialize (MC eq_refl). dand MC as (A1 & A2 & A3 & A4 & _ & _ & CT). clear Mo.
  unfold ctable_live in CT. cbn [t_lc t_lb t_nx] in CT.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf CT. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1 H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [intros _; split_conj; try assumption; unfold ctable_live; cbn [t_lc t_lb t_nx]; exact CT |].
    split_conj; mode_vacuous.
  - clear - H8. lia_std.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CL.
Hypothesis CLDONE : cldone_stmt.

Theorem clhead_s : clhead_stmt.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. pose proof KM as KM0.
  open_K K. open_kmem KM. pose proof STD as STD0. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (MC : t_mode st = CODELENS -> 257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            t_shave st <= t_nlen st + t_ndist st /\ (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) by mode_get MODE_.
  specialize (MC Hm). dand MC as (Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hsh & Hlf15 & CT). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold ctable_live in CT. cbn [t_lc t_lb t_nx] in CT. dand CT as (Hlc & Hlb & Hnx0 & Hnx1 & TOK). cbv [N_CODES] in Hnx1.
  assert (HJ : forall (jo : Z) (Mq : mem), PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
      (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf jo Mq ->
      mem_u64 R_segs Mq (u + -136) 67008).
  { intros jo Mq HPq. destruct HPq as (STDq & _). unfold s_std in STDq. destruct STDq as (_ & _ & _ & _ & _ & FRMq & _).
    pose proof (i_frame_slots _ _ FRMq) as FSq. icx_cbn. cbv [JTAB_ADDR] in FSq.
    dand FSq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S136q). exact S136q. }
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  unfold s_regs_cl, s_fix, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn.
  dand SR' as (_ & _ & _ & _ & _ & _ & _ & C104 & _ & C120 & _ & _ & C132 & C136 & C140 & _).
  subst lc. cbv [cp_addr o_codes] in C104. icx_cbn.
  assert (Hshv : 0 <= shave) by (pose proof (Hlf15 0); lia).
  (* [comment removed for export] *)
  pose proof (PL_intro _ _ _ _ _ _ _ KM0) as [HP _]. cbn [t_shave] in HP.
  clear Ww CST HK Hmode SREST SRET SOUT.
  prune_rng.
  zkeysb. unfold L_CL_HEAD, L_CL_DONE, L_CL_LOOP, L_LVX_CL, L_LEAVE_A7, L_BADREP0, L_BADREP, L_BADMSG_S11, L_LEAVE, L_LEAVE_LD in *.
  cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  destruct (Z_lt_dec shave (nlen + ndist)) as [Hgo | Hdone0].
  2: { (* [comment removed for export] *)
    zbr Rfd true.                     (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLDONE (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI0) end.
    - unfold s_regs_cld, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - exact KM0.
    - exact KA0. }
  zbr Rfd false.                      (* [comment removed for export] *)
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  zsetreg (2 ^ lb - 1) ltac:(symmetry; apply mask_not_sllw; lia).
  zstep Rfd.                          (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (KMX : forall M' (ci' H' B' j' : Z) (lf' : Z -> Z),
    PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
       (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf j' M' ->
    mem_arr 2 R_segs M' (p + 168) 320 lf' ->
    k_mem (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
      (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j') lf' cf M').
  { intros M' ci' H' B' j' lf' HP' HL'. unfold st_cl. ist_cbn.
    pose proof (PL_kmem _ _ _ _ lf' _ _ _ HP' HL') as X. unfold st_sh in X. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in X.
    unfold k_mem in X |- *. dand X as (X1 & X2 & X3 & X3b & X4 & X5 & X6). split_conj; try assumption. }
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (cl_loop (S (Z.to_nat (nlen + ndist - shave)))
              (PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                  (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf)
              Rx lx Mx MD T u p q n nlen (nlen + ndist) lb (2 ^ lb - 1) nx cin bits shave cin bits hold fin cf lf Hh) end;
    try zreg; try lia; try eassumption; try reflexivity.
  - unfold ZSEP. pose proof (sep_p_q _ _ SEP) as D. cbn [c_p c_q c_n] in D. cbv [STATE_SIZE] in D. exact D.
  - intros M' jo a v HPj Ha Hv. apply (PL_store140 _ _ _ _ _ _ _ _ _ CX0 HPj); [icx_cbn; exact Ha | exact Hv].
  - intros M' jo a v HPj Ha1 Ha2. apply (PL_store_lens _ _ _ _ _ _ _ _ _ CX0 HPj); icx_cbn; lia.
  - (* [comment removed for export] *)
    intros R' M' j' ci0 B0 H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. zkeys.
    match goal with HP' : PL _ _ _ _ _ j' M' |- _ =>
      dand HP' as (STD' & SAT' & SRET' & SOUT' & HC' & HAG'); unfold s_ret in SRET'; unfold st_sh in SAT'; icx_cbn end.
    eapply (stub_CL R' [] M' MD T q n ci0 B0 u ret Hh); try (cbv [zget_l alookup]; eassumption); try lia.
    intros R9 E9 E27 E2 HK9. kopen HK9.
    pose proof (sinv_cl _ _ lf cf n H' (B0 + 8 * (n - ci0)) j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KL Rx Mx _ ret lf' cf SI1) end.
    + unfold s_regs_leave, st_cl; icx_cbn; zkeys; split_conj; kgoal.
    + exact STD'.
    + unfold st_cl; ist_cbn. exact SAT'.
    + unfold st_cl, s_out in *; ist_cbn. exact SOUT'.
    + assumption.
    + exact HC'.
    + exact HAG'.
  - (* [comment removed for export] *)
    intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. unfold L_LEAVE_A7. zkeys.
    match goal with HP' : PL _ _ _ _ _ j' M' |- _ =>
      dand HP' as (STD' & SAT' & SRET' & SOUT' & HC' & HAG'); unfold st_sh in SAT'; icx_cbn end.
    zstep Rfd.                        (* [comment removed for export] *)
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf' cf SI1) end.
    + unfold s_regs_leave_ld, st_cl; icx_cbn; zkeys; split_conj; kgoal.
    + exact STD'.
    + unfold st_cl; ist_cbn. exact SAT'.
    + unfold st_cl, s_ret in *; ist_cbn. exact SRET'.
    + unfold st_cl, s_out in *; ist_cbn. exact SOUT'.
    + assumption.
    + exact HC'.
    + exact HAG'.
  - (* [comment removed for export] *)
    intros pc R' M' j' ci' B' H' lf' Hpc. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. unfold L_BADREP0, L_BADREP in Hpc. zkeys.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j')) as MB.
    unfold st_cl in MB, SI1, ME1 |- *. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in MB, SI1, ME1 |- *. change (rank CODELENS) with 20 in MB.
    destruct Hpc as [-> | ->];
      (zstep Rfd; zstep Rfd; zlit;    (* [comment removed for export] *)
       zstep Rfd;                      (* [comment removed for export] *)
       lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
         eapply (KB11 Rx Mx (IST CODELENS last flags ci' cout H' B' out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist j' nx whave wnext) lf' cf
                   (sinv_bad_of _ _ _ _ SI1)) end;
       [ clear - MB ME1; lia
       | unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; kgoal
       | lazymatch goal with |- 0 <= ?x < _ => first [ assert (EA2 : x = 66210) by zreg; rewrite EA2 | assert (EA2 : x = 66272) by zreg; rewrite EA2 ] end; lia
       | apply KMX; assumption ]).
  - (* [comment removed for export] *)
    intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. zkeys.
    assert (Ej : j' = nlen + ndist) by lia.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLDONE (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j')
                lf' cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end.
    + unfold s_regs_cld, s_fix, s_vars, st_cl; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; kgoal.
    + apply KMX; assumption.
    + eapply KALL_mono; [| exact KA0]. clear - ME1. unfold st_cl in ME1. exact ME1.
Qed.

(* [comment removed for export] *)
Theorem arm_CODELENS_s0 : arm_stmt L_CODELENS CODELENS.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode] in Hm. subst mode.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  unfold st_rest in SREST. icx_cbn. dand SREST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C140 & _).
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & Mo). unfold RNG in RNG_. icx_cbn. destr_conj RNG_.
  assert (MC : CODELENS = CODELENS -> 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\ shave <= nlen + ndist /\
            (forall i, 0 <= i < shave -> lf i <= 15) /\
            ctable_live (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  specialize (MC eq_refl). dand MC as (MC1 & MC2 & MC3 & MC4 & MC5 & _). clear Mo.
  zkeysb. unfold L_CODELENS, L_CL_HEAD in *. pose proof two64_eq as TW64.
  tstep1 Rfd.                         (* [comment removed for export] *)
  zstep Rfd.                          (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (clhead_s (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx lx Mx
              (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI) end.
  - unfold s_regs_cl, s_fix, s_vars; icx_cbn; zkeys; split_conj; zreg.
  - exact KM0.
  - exact K.
Qed.

End CL.
End FXG.
End S_Codelens.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.I9S Require Import SBase. Import S_ClDefs. Import S_Table. Import S_CodelensT. Import S_Codelens.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.
Theorem arm_TABLE_s : itable_spec_s -> ifast_spec_s -> arm_stmt L_TABLE TABLE.
Proof. intros IT IFA. exact (arm_TABLE_s0 IT (clhead_s (cldone_s IT IFA))). Qed.

Theorem arm_LENLENS_s : itable_spec_s -> ifast_spec_s -> arm_stmt L_LENLENS LENLENS.
Proof. intros IT IFA. exact (arm_LENLENS_s0 IT (clhead_s (cldone_s IT IFA))). Qed.

Theorem arm_CODELENS_s : itable_spec_s -> ifast_spec_s -> arm_stmt L_CODELENS CODELENS.
Proof. intros IT IFA. exact (arm_CODELENS_s0 (cldone_s IT IFA)). Qed.
End FXG.
