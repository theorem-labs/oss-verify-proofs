(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import SFModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import SysStep Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio ZApi ZHarness ZApiL ZHarnessL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Printf_lib F_printf_iface F_vfprintf F_vsnprintf. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Printf_pieces. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Printf_stdio_iface Printf_bridge F_fprintf. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Zh_pieces.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).

Definition A_FMT_err : Z := 0x102f2.          (* [comment removed for export] *)
Definition A_FMT_bad : Z := 0x1048f.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition harness_names : list (Z * list Z * list Z) :=
  [ (0x102ae, NL_deflateInit, [105; 110; 118; 97; 108; 105]);
    (0x1037f, NL_deflate1, [0; 46; 0]);
    (0x104f8, NL_deflate2, [105; 110; 118; 97; 108; 105]);
    (0x103f8, NL_deflate3, [115; 116]);
    (0x1030b, NL_deflateEnd, [105; 110; 118; 97]);
    (0x102a2, NL_inflateInit, [100; 101]);
    (0x104df, NL_inflate, [102; 105; 108]);
    (0x10346, NL_inflateEnd, [105; 110; 118; 97; 108; 105; 100]) ].
Definition harness_name (An : Z) (name : list Z) : Prop := exists slack, In (An, name, slack) harness_names.

(* [comment removed for export] *)
Definition name_okb (e : Z * list Z * list Z) : bool :=
  let '(An, name, slack) := e in
  ro_bytes_b psegs An (zb (name ++ 0 :: slack)) && forallb (fun c => (0 <? c) && (c <? 256)) name
  && ((- (An + zlength name + 1)) mod 8 <=? zlength slack) && (0x10000 <=? An) && (An + zlength name + 1 + zlength slack <=? 0x29000)
  && (zlength name <=? 15).
Lemma harness_names_ok : forallb name_okb harness_names = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition FMT_badL : list Z := (str "bad large inflate: %zu" ++ [10; 0])%list.
Definition pieces_badL (u : Z) : list (list Z) :=
  ([str "bad large inflate: "%string; []] ++ (if u =? 0 then [[]; [48]; []] else [[]; dec_digits u]) ++ [[10]])%list.

Lemma Zdecimal_0 : Zdecimal 0 = [48].
Proof. reflexivity. Qed.

Lemma pieces_badL_concat : forall u, 0 <= u < 2^64 -> List.concat (pieces_badL u) = msgl_bad u.
Proof.
  intros u Hu. unfold pieces_badL, msgl_bad.
  destruct (Z.eqb_spec u 0) as [->|NZ].
  - rewrite Zdecimal_0. reflexivity.
  - replace (u =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite (Zdecimal_dec u) by lia.
    cbn [List.concat app]. reflexivity.
Qed.

Lemma pieces_badL_len : forall u, 0 <= u < 2^64 -> 20 <= zlength (List.concat (pieces_badL u)) <= 40.
Proof.
  intros u Hu. rewrite (pieces_badL_concat u Hu). unfold msgl_bad.
  destruct (Z.eq_dec u 0) as [->|NZ].
  - rewrite Zdecimal_0. vm_compute. split; discriminate.
  - rewrite (Zdecimal_dec u) by lia. pose proof (dec_digits_zlength u) as DL. pose proof (dec_digits_nz u ltac:(lia)) as NE.
    assert (L1 : 1 <= zlength (dec_digits u)) by (destruct (dec_digits u); [contradiction| unfold zlength; cbn; lia]).
    unfold zlength in *. rewrite !length_app. cbn [Datatypes.length]. change (Datatypes.length (str "bad large inflate: ")) with 19%nat. lia.
Qed.

Lemma printf_pieces_badL : forall u, 0 <= u < 2^64 ->
  printf_pieces FMT_badL [PA_z u] = Some (pieces_badL u, 19 + (if u =? 0 then 1 else zlength (dec_digits u)) + 1).
Proof.
  intros u Hu. pose proof (dec_digits_zlength u) as DL. unfold printf_pieces.
  change (Datatypes.length FMT_badL) with 24%nat.
  ppl_step. ppl_step.
  pose proof (conv_pieces_zu 19 u ltac:(lia) Hu ltac:(unfold INT_MAX; lia)) as C2. cbv delta [T_SIZET] in C2. rewrite C2. clear C2.
  remember (if u =? 0 then [[]; [48]; []] else [[]; dec_digits u]) as P2 eqn:EP2.
  remember (if u =? 0 then 1 else zlength (dec_digits u)) as l2 eqn:El2.
  assert (Hl2 : 0 <= l2 <= 20) by (subst l2; destruct (u =? 0); lia).
  rewrite (ppl_noargs_shift 22 [10; 0] (19 + l2) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
  unfold pieces_badL. subst P2. cbn [app]. destruct (u =? 0); reflexivity.
Qed.

Lemma pass1_ok_badL : pass1_ok FMT_badL = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_calls_badL : forall u, fp_calls (Datatypes.length FMT_badL) FMT_badL [PA_z u] = [].
Proof. intros. reflexivity. Qed.

Section CheckErr.
  Context {St : Type}.
  Hypothesis FWE : fwritex_stderr_stmt.
  Hypothesis FLS : stdio_write_flush_stmt.

  Definition check_err_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  Definition check_err_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (An : Z) (name : list Z) (rc : Z),
      stderr_wfile0 m ->
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A_FMT_err -> a2 = Z_to_bv 64 An -> harness_name An name ->
      - 2^31 <= rc < 2^31 -> bv_unsigned a3 mod 2^32 = rc mod 2^32 ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      Monad.implM psegs (stderr_fprintf (St:=St) [msg_err name rc]) st
            (check_err_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x227e4) fc None m (seg_rom psegs)).

  Theorem check_err_proof : check_err_stmt.
  Proof using FLS FWE.
    unfold check_err_stmt. intros until rc. intros SF Ha0 Ha1 Ha2 [slack HN] RC Ha3 ST LO GLO QHI SSP MI FRM.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    (* [comment removed for export] *)
    pose proof (proj1 (forallb_forall _ _) harness_names_ok _ HN) as OKB. unfold name_okb in OKB.
    rewrite !andb_true_iff in OKB. destruct OKB as (((((RB & NR) & SLK) & ALO) & AHI) & NLEN).
    apply Z.leb_le in SLK, ALO, AHI, NLEN.
    assert (NRF : Forall (fun c => 0 < c < 256) name).
    { apply Forall_forall. intros c Hc. pose proof (proj1 (forallb_forall _ _) NR c Hc) as X. apply andb_prop in X. destruct X as [X1 X2].
      apply Z.ltb_lt in X1, X2. lia. }
    pose proof (zlength_nonneg' name) as NL0. pose proof (zlength_nonneg' slack) as SL0.
    (* [comment removed for export] *)
    pose proof (pieces_err_concat name rc RC) as CC. pose proof (pieces_d_len rc RC) as DL.
    assert (ML : zlength (List.concat (pieces_err name rc)) <= INTERNAL_BUFSIZ).
    { unfold pieces_err. rewrite concat_app. cbn [List.concat app]. rewrite concat_app. cbn [List.concat app]. rewrite app_nil_r.
      unfold zlength in *. rewrite !length_app. cbn [Datatypes.length]. change (Datatypes.length (str " error: "%string)) with 8%nat.
      unfold INTERNAL_BUFSIZ. lia. }
    unfold Monad.implM. rewrite <- CC. rewrite <- (stderr_fprintf_concat (pieces_err name rc) st ML).
    (* [comment removed for export] *)
    unfold stderr_fprintf.
    eapply impl_epost_mono.
    - eapply (stderr_bridge psegs (pieces_err name rc) [] st (fun s' ms' => check_err_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms')).
      + unfold pieces_err, pieces_d, OUT_MAX.
        assert (D1 : forall x, zlength (dec_digits x) <= 2^25) by (intros x; pose proof (dec_digits_zlength x); lia).
        repeat (apply Forall_cons; [ first [ change (zlength (@nil Z)) with 0; lia | lia | vm_compute; discriminate ] | ]).
        apply Forall_app. split; [| repeat constructor; vm_compute; discriminate].
        destruct (rc <? 0); [| destruct (rc =? 0)]; repeat (apply Forall_cons; [ first [ apply D1 | vm_compute; discriminate ] | ]); apply Forall_nil.
      + eapply impl_mono; [eapply (impl_tforall psegs (at_node psegs) _ _ _ _ (outsk_flush_leaves (pieces_err name rc) [] st))|].
        * pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG.
          unfold Monad.implM in FG.
          eapply FG with (fmt := FMT_err) (args := [PA_s name; PA_i rc]) (A := A_FMT_err) (lo := lo) (canary := canary); clear FG;
            [ exact Ha0 | exact Ha1 | apply stderr_wfile0_wfile; exact SF
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_err; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | apply pass1_ok_err
            |
            | apply printf_pieces_err; [lia| exact RC]
            | apply fp_calls_err
            | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM
            | unfold A_FMT_err; lia
            | vm_compute; discriminate ].
          (* [comment removed for export] *)
          cbn [args_ok arg_ok]. split; [| split; [| exact I]].
          -- exists (zb slack). subst a2. rewrite unsigned_lit by lia.
             assert (BY : bytes_at psegs m An (zb (name ++ 0 :: slack))).
             { apply fmt_bytes_at; [exact MI| exact RB| lia|]. unfold zlength in *. rewrite length_app. cbn [Datatypes.length]. lia. }
             unfold zb in BY |- *. rewrite map_app in BY. cbn [map] in BY.
             unfold FPRINTF_DEPTH, GLOBALS_TOP, VF_FRAME in *. unfold zlength in *. rewrite length_map.
             repeat (split; [first [exact BY | exact NRF | lia] |]). lia.
          -- split; [exact RC|]. exact Ha3.
        * intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|].
          destruct H1 as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP').
          exists x5, x6, x7, b0, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', m'.
          repeat (split; [assumption|]). exact H2.
    - intros [[] s'] ms' H'. exact H'.
  Qed.

  (* [comment removed for export] *)
  Definition bad_msg_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (u : Z),
      stderr_wfile0 m ->
      a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A_FMT_bad -> 0 <= u < 2^64 -> bv_unsigned a2 = u ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
      Monad.implM psegs (stderr_fprintf (St:=St) [msgl_bad u]) st
            (check_err_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x227e4) fc None m (seg_rom psegs)).

  Theorem bad_msg_proof : bad_msg_stmt.
  Proof using FLS FWE.
    unfold bad_msg_stmt. intros until u. intros SF Ha0 Ha1 UR Ha2 ST LO GLO QHI SSP MI FRM.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (pieces_badL_concat u UR) as CC. pose proof (pieces_badL_len u UR) as DL.
    assert (ML : zlength (List.concat (pieces_badL u)) <= INTERNAL_BUFSIZ) by (unfold INTERNAL_BUFSIZ; lia).
    unfold Monad.implM. rewrite <- CC. rewrite <- (stderr_fprintf_concat (pieces_badL u) st ML).
    unfold stderr_fprintf.
    eapply impl_epost_mono.
    - eapply (stderr_bridge psegs (pieces_badL u) [] st (fun s' ms' => check_err_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms')).
      + unfold pieces_badL, OUT_MAX.
        assert (D1 : forall x, zlength (dec_digits x) <= 2^25) by (intros x; pose proof (dec_digits_zlength x); lia).
        apply Forall_app. split; [repeat constructor; vm_compute; discriminate|].
        apply Forall_app. split; [| repeat constructor; vm_compute; discriminate].
        destruct (u =? 0); repeat (apply Forall_cons; [ first [ apply D1 | vm_compute; discriminate ] | ]); apply Forall_nil.
      + eapply impl_mono; [eapply (impl_tforall psegs (at_node psegs) _ _ _ _ (outsk_flush_leaves (pieces_badL u) [] st))|].
        * pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG.
          unfold Monad.implM in FG.
          eapply FG with (fmt := FMT_badL) (args := [PA_z u]) (A := A_FMT_bad) (lo := lo) (canary := canary); clear FG;
            [ exact Ha0 | exact Ha1 | apply stderr_wfile0_wfile; exact SF
            | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_bad; lia | vm_compute; discriminate]
            | apply forall_range_b; vm_compute; reflexivity
            | apply pass1_ok_badL
            |
            | apply printf_pieces_badL; exact UR
            | apply fp_calls_badL
            | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM
            | unfold A_FMT_bad; lia
            | vm_compute; discriminate ].
          (* [comment removed for export] *)
          cbn [args_ok arg_ok]. split; [exact Ha2| exact I].
        * intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|].
          destruct H1 as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP').
          exists x5, x6, x7, b0, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', m'.
          repeat (split; [assumption|]). exact H2.
    - intros [[] s'] ms' H'. exact H'.
  Qed.
End CheckErr.
