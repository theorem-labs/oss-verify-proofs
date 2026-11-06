(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayoutC ArgvEnvC
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AsanCeil.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := target_alloc_limit.
(* [comment removed for export] *)
Definition LIM_MIN : Z := 2 ^ 33.
Lemma LIMIT_ok : LIM_MIN <= LIMIT. Proof. unfold LIM_MIN, LIMIT, target_alloc_limit. lia. Qed.
Lemma SRC_LIMIT_ok : LIM_MIN <= source_alloc_limit. Proof. unfold LIM_MIN, source_alloc_limit. lia. Qed.

(* [comment removed for export] *)
Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
  if_ph    : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
  if_hull  : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
  if_top   : reserved_top (segments_reserved segs) = img_hi A;
  if_res   : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                    (segments_reserved segs);
  if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
  if_rw    : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
             /\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
  if_shadow : 0 <= shadow_off A <= 2 ^ 47
}.

(* [comment removed for export] *)
Definition stack_image_size (argv envp : list (list byte)) : Z :=
  let struct_size := (8 + (Z.of_nat (length argv) + 1) * 8
                      + (Z.of_nat (length envp) + 1) * 8 + 160)%Z in
  let len := (struct_size + total_arg_bytes argv + total_arg_bytes envp)%Z in
  (len + ((8 - len mod 8) mod 8) + 16)%Z.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [comment removed for export] *)
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* [comment removed for export] *)
  Variable nofile : word.
  Variable sigmask : word.
  (* [comment removed for export] *)
  Variable urnd : InputStream.
  (* [comment removed for export] *)
  Variable LIM : Z.
  Hypothesis HLIM : LIM_MIN <= LIM.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Huid : valid_id uid.
  (* [comment removed for export] *)
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).

  (* [comment removed for export] *)
  Definition inp : ProcInput := mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd [].  (* [comment removed for export] *)
  Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.
  Let SIMG := entry_stack_image ph sp argv envp uid hw rdraw.   (* [comment removed for export] *)
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [comment removed for export] *)
  Let W := (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) / 8.
  (* [comment removed for export] *)
  Let PGSP := pgdown usp.
  Let PGTOP := (usp + Z.of_nat (length bsb) + 4095) / 4096 * 4096.
  Let Q := (PGTOP - PGSP) / 4096.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 4096) / 16); Z_to_bv 64 L1; uid; hw;
     Z_to_bv 64 ((usp mod 32768) / 4096); Z_to_bv 64 Q].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* [comment removed for export] *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    (((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
     || ((usp + 8 * argc + 8 * envc + 184 <=? z) && (z <? usp + 8 * argc + 8 * envc + 184 + 8 * W)))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem ph sp argv envp uid hw rdraw a).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a /\ usp <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
    pose proof (valid_argv_len argv Hva).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold usp, argc, envc in H |- *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma NX0_spw : AP.expr_vars_lt NX0 e_spw = true.
  Proof. reflexivity. Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof. reflexivity. Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M [Hag _] [H1 H2]. split; [|exact H2]. intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.

  (* [comment removed for export] *)
  Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size argv envp.
  Proof.
    unfold bsb, build_stack_bytes, stack_image_size. cbv zeta.
    rewrite (string_addrs_pair argv). cbv beta iota.
    rewrite (string_addrs_pair envp). cbv beta iota.
    rewrite !length_app, length_at_random_bytes, repeat_length, !length_flat_map_le8,
      !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
      !length_flatten_strings.
    rewrite !total_arg_bytes_Z. unfold auxv_size.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    match goal with
    | |- context [Z.to_nat ?pd] =>
        assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia); rewrite (Z2Nat.id pd) by lia
    end.
    lia.
  Qed.

  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    pose proof (build_stack_bytes_within_span ph sp argv envp uid hw rdraw) as B. fold bsb in B.
    unfold entry_stack_fits, sp_window_hi in Hfit. unfold usp. lia.
  Qed.

  Lemma bsb_ge : 8 * argc + 8 * envc + 200 <= Z.of_nat (length bsb) /\ (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) mod 8 = 0.
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size, argc, envc. cbv zeta.
    pose proof (total_arg_bytes_Z argv). pose proof (total_arg_bytes_Z envp).
    match goal with |- context [((8 - ?l mod 8) mod 8)%Z] => set (len := l) end.
    assert (0 <= Z.of_nat (total_arg_bytes_nat argv)) by lia.
    split; [lia|].
    assert (Hpd : 0 <= (8 - len mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hm : (len + (8 - len mod 8) mod 8) mod 8 = 0).
    { rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
      replace (len mod 8 + (8 - len mod 8)) with 8 by lia. reflexivity. }
    replace (len + (8 - len mod 8) mod 8 + 16 - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184))
      with (len + (8 - len mod 8) mod 8 - 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 23)) by (unfold len; lia).
    rewrite Zminus_mod, Hm, Z.mul_comm, Z_mod_mult. reflexivity.
  Qed.

  Lemma W_range : 0 <= W /\ 8 * W = Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184) /\ W <= 280000.
  Proof.
    pose proof bsb_ge as [G M]. pose proof (bsb_bound ph sp argv envp uid hw rdraw Hva Hve) as B. fold bsb in B.
    unfold W. pose proof len_av. pose proof len_ev.
    lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge as [G _]. pose proof len_av. pose proof len_ev. lia. Qed.

  (* [comment removed for export] *)
  Ltac mod_small_inner :=
    repeat match goal with
      |- context [ (?a mod ?m) ] =>
        lazymatch a with context [ _ mod _ ] => fail | _ => rewrite (Z.mod_small a m) by lia end
    end.

  (* [comment removed for export] *)
  Ltac hide_lets := first [clearbody Q | idtac]; first [clearbody PGTOP | idtac]; first [clearbody PGSP | idtac].

  (* [comment removed for export] *)
  Lemma usp_decomp :
    usp = 32768 * (usp / 32768) + 4096 * ((usp mod 32768) / 4096) + 16 * ((usp mod 4096) / 16)
    /\ 0 <= (usp mod 32768) / 4096 <= 7 /\ 0 <= (usp mod 4096) / 16 <= 255 /\ usp mod 4096 = 16 * ((usp mod 4096) / 16)
    /\ usp mod 32768 = 4096 * ((usp mod 32768) / 4096) + usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_al.
    pose proof (Z.div_mod usp 32768 ltac:(lia)). pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)).
    pose proof (Z.div_mod (usp mod 32768) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (usp mod 32768) 4096 ltac:(lia)).
    pose proof (Z.div_mod usp 4096 ltac:(lia)). pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)).
    pose proof (Z.div_mod (usp mod 4096) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (usp mod 4096) 16 ltac:(lia)).
    pose proof (Z.div_mod usp 16 ltac:(lia)).
    assert (E1 : (usp mod 32768) mod 4096 = usp mod 4096).
    { apply Z.mod_mod_divide. exists 8. reflexivity. }
    pose proof (Z.div_mod (usp mod 32768) 4096 ltac:(lia)) as D2. rewrite E1 in D2.
    assert (E2 : (usp mod 4096) mod 16 = 0).
    { rewrite Z.mod_mod_divide by (exists 256; reflexivity). exact usp_al. }
    assert ((usp mod 32768) / 4096 < 8) by (apply Z.div_lt_upper_bound; lia).
    assert ((usp mod 4096) / 16 < 256) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos (usp mod 32768) 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (usp mod 4096) 16 ltac:(lia) ltac:(lia)).
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma PG_range : PGSP <= usp < PGSP + 4096 /\ usp + Z.of_nat (length bsb) <= PGTOP < usp + Z.of_nat (length bsb) + 4096
                   /\ PGTOP <= 2 ^ 47 /\ PGSP mod 4096 = 0 /\ PGTOP mod 4096 = 0 /\ PGTOP = PGSP + 4096 * Q /\ 1 <= Q <= 600.
  Proof.
    pose proof usp_lo. pose proof usp_fit as F. pose proof bsb_ge as [G _]. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    unfold Q, PGTOP, PGSP, pgdown.
    set (t := usp + Z.of_nat (length bsb)). assert (Ht : t = usp + Z.of_nat (length bsb)) by reflexivity.
    pose proof (Z.div_mod usp 4096 ltac:(lia)) as Du. pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)) as Mu.
    pose proof (Z.div_mod (t + 4095) 4096 ltac:(lia)) as Dt. pose proof (Z.mod_pos_bound (t + 4095) 4096 ltac:(lia)) as Mt.
    set (q1 := usp / 4096) in *. set (r := usp mod 4096) in *. set (q2 := (t + 4095) / 4096) in *. set (r2 := (t + 4095) mod 4096) in *.
    replace (usp - r) with (q1 * 4096) by lia.
    replace (q2 * 4096 - q1 * 4096) with ((q2 - q1) * 4096) by lia.
    rewrite (Z.div_mul (q2 - q1) 4096) by lia.
    assert (M1 : (q1 * 4096) mod 4096 = 0) by apply Z_mod_mult. assert (M2 : (q2 * 4096) mod 4096 = 0) by apply Z_mod_mult.
    clearbody q1 r q2 r2 t W.
    assert (Q2 : q2 <= 2 ^ 35) by lia.
    repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    pose proof usp_decomp as (_ & _ & D3 & _).
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma uE0_PQ : uE E0 (EVar V_P) = (usp mod 32768) / 4096 /\ uE E0 (EVar V_Q) = Q.
  Proof.
    pose proof usp_decomp as (_ & D2 & _). pose proof PG_range as (_ & _ & _ & _ & _ & _ & QR).
    unfold uE. cbn [edenot E0 ev nth vals0 V_P V_Q]. rewrite !u64_lit by lia. split; reflexivity.
  Qed.

  Lemma L1_range : 0 <= L1 <= 131071.
  Proof.
    unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
  Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.

  Lemma edenot_uid : uid = edenot E0 (EVar V_UID).
  Proof. reflexivity. Qed.

  Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma u_e_pgsp : uE E0 e_pgsp = usp - usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). destruct uE0 as (U1 & U2 & _). destruct uE0_PQ as [UP _].
    unfold e_pgsp, eadd, escale, uE in *. unfold V_S1, V_P in U1, UP. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). destruct uE0 as (U1 & U2 & _). destruct uE0_PQ as [UP _].
    unfold e_sp0, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, UP.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma u_e_spw : uE E0 e_spw = usp.
  Proof. replace e_spw with e_sp0 by (vm_compute; reflexivity). exact u_e_sp0. Qed.
  (* [comment removed for export] *)
  Lemma SINV0_pgsp : forall E M, SINV0 E M -> uE E e_pgsp = pgdown usp.
  Proof.
    intros E M [H1 _]. unfold pgdown. rewrite <- u_e_pgsp. unfold uE, e_pgsp, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    cbn [edenot]. rewrite (H1 0%nat), (H1 10%nat) by (unfold NX0; lia). reflexivity.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  Lemma u_sp8 : uE E0 e_sp8 = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). destruct uE0 as (U1 & U2 & _). destruct uE0_PQ as [UP _].
    unfold e_sp8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, UP.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_envp : uE E0 e_envp = usp + 8 * argc + 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (_ & _ & U3 & _).
    pose proof u_e_sp0 as US. unfold e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_auxv : uE E0 e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & _ & U4 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U4.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str0 : uE E0 e_str0 = usp + 8 * argc + 8 * envc + 184.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof u_e_auxv as UA. unfold e_str0, eaddz, uE in *. rewrite mkAlu_denot, edenot_lit.
    rewrite u_add64, u64_lit by lia. rewrite UA. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str1 : uE E0 e_str1 = usp + 8 * argc + 8 * envc + 184 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_atrandom : uE E0 e_atrandom = usp + Z.of_nat (length bsb) - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_str0 as US. unfold e_atrandom, eadd, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, edenot_lit.
    rewrite u_add64, u_mul64, u64_lit by lia. rewrite US, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + W.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). pose proof u_sp8 as U8.
    unfold e_atr8, eadd, uE in *. rewrite !mkAlu_denot. cbn [edenot]. cbn [edenot] in U3, U4, U6.
    rewrite !u_add64. rewrite U8, U3, U4, U6.
    assert (usp / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 8 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition Xsh : Z := argc + envc + W + 2 * ((usp mod 4096) / 16).   (* [comment removed for export] *)
  Lemma Xsh_range : 1 <= Xsh <= 1024 + 256 + 280000 + 510.
  Proof. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3). unfold Xsh. pose proof usp_decomp as (_ & _ & D3 & _). lia. Qed.
  Lemma u_e_Xsh : uE E0 e_Xsh = Xsh.
  Proof.
    pose proof Xsh_range. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3). pose proof usp_decomp as (_ & _ & D3 & _).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). unfold uE in *.
    unfold e_Xsh, Xsh, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U2, U3, U4, U6.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U2, U3, U4, U6.
    assert (Hu : 0 <= usp mod 4096 / 16 < 256).
    { pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)) as B. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    set (u := usp mod 4096 / 16) in *. clearbody u.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_e_Xm : uE E0 e_Xm = Xsh - Xsh mod 8.
  Proof.
    pose proof Xsh_range. pose proof u_e_Xsh as UX. unfold uE in *.
    unfold e_Xm. rewrite mkAlu_denot, edenot_lit. rewrite u_and64. rewrite UX.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 2 ^ 3)%Z by reflexivity. rewrite land_highmask by lia. reflexivity.
  Qed.
  Lemma u_e_atr8m : uE E0 e_atr8m = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096) + (Xsh - Xsh mod 8).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof Xsh_range. pose proof (Z.mod_pos_bound Xsh 8 ltac:(lia)). pose proof usp_decomp as (_ & D2 & _).
    destruct uE0 as (U1 & _). destruct uE0_PQ as [UP _]. pose proof u_e_Xm as UM. unfold uE in *.
    unfold e_atr8m, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U1, UP, UM. rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UM.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. reflexivity.
  Qed.
  Lemma e_atr8m_range : 0xFFFF0000000 <= uE E0 e_atr8m <= 0xFFFFFFFFFE0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof W_range as (W1 & W2 & W3). pose proof bsb_ge as [G _]. pose proof Xsh_range as XR. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5).
    rewrite u_e_atr8m.
    (* [comment removed for export] *)
    set (s1 := usp / 32768) in *. set (p := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    pose proof (Z.div_mod Xsh 8 ltac:(lia)) as D6. pose proof (Z.mod_pos_bound Xsh 8 ltac:(lia)) as M6.
    set (m := Xsh mod 8) in *. set (xq := Xsh / 8) in *. unfold Xsh in *.
    assert (U8 : usp = 8 * (4096 * s1 + 512 * p + 2 * s2)) by lia.
    nia.
  Qed.
  Lemma u_e_vis3b : uE E0 e_vis3b = 32768 * (usp / 32768).
  Proof.
    pose proof usp_lo. pose proof usp_hi. destruct uE0 as (U1 & _). unfold uE in *.
    unfold e_vis3b, escale. rewrite mkMd_denot, edenot_lit, u_mul64, u64_lit by lia. rewrite U1.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite Z.mod_small by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma targ_ge : L0 + L1 + 1 <= total_arg_bytes argv.
  Proof.
    unfold L0, L1. pose proof Hav0 as H0. destruct argv as [|a0 [|a1 rest]]; [cbn in H0; lia| |].
    - cbn -[Z.of_nat Z.add]. lia.
    - cbn -[Z.of_nat Z.add total_arg_bytes]. change (total_arg_bytes (a0 :: a1 :: rest)) with (Z.of_nat (length a0) + 1 + (Z.of_nat (length a1) + 1 + total_arg_bytes rest)).
      pose proof (total_arg_bytes_nonneg rest). lia.
  Qed.
  Lemma W8_ge : L0 + L1 + 1 <= 8 * W.
  Proof.
    pose proof W_range as (W1 & W2 & W3). pose proof targ_ge. pose proof length_bsb_eq as LB.
    unfold stack_image_size in LB. cbv zeta in LB.
    pose proof (total_arg_bytes_nonneg envp).
    match type of LB with context [((8 - ?l mod 8) mod 8)%Z] => pose proof (Z.mod_pos_bound (8 - l mod 8) 8 ltac:(lia)) end.
    unfold argc, envc in *. lia.
  Qed.
  Lemma u_e_blk : uE E0 e_blk0 = PGTOP - (usp + 8 * argc + 8 * envc)
                  /\ uE E0 e_blkL0 = PGTOP - (usp + 8 * argc + 8 * envc) - L0
                  /\ uE E0 e_blkL01 = PGTOP - (usp + 8 * argc + 8 * envc) - L0 - L1
                  /\ uE E0 e_strW0 = 8 * W - L0 /\ uE E0 e_strW01 = 8 * W - L0 - L1
                  /\ uE E0 e_blk08 = (PGTOP - (usp + 8 * argc + 8 * envc)) / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3). pose proof bsb_ge as [G GM].
    pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P2 & P3 & P4 & P5 & P6 & QR). pose proof W8_ge. pose proof L1_range.
    assert (HL0 : 0 <= L0 <= 131071) by (unfold L0; pose proof (valid_argv_str_len argv 0 Hva Hav0); lia).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). destruct uE0_PQ as [UP UQ]. pose proof uE0_L1 as UL1. unfold uE in *.
    unfold PGSP, pgdown in P1, P6.
    (* [comment removed for export] *)
    set (s1 := usp / 32768) in *. set (pp := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    clearbody s1 pp s2. first [clearbody Q | idtac]. first [clearbody PGTOP | idtac]. first [clearbody W | idtac]. first [clearbody PGSP | idtac].
    unfold e_blk0, e_blkL0, e_blkL01, e_strW0, e_strW01, e_blk08, e_blk0, esub, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, ?mkAlu_denot, !edenot_lit.
    cbn [edenot]. cbn [edenot] in U2, U3, U4, U5, U6, UQ, UL1.
    rewrite ?u_sub64, ?u_mul64, ?u_add64, ?u_mul64, ?u_add64. rewrite !u64_lit by lia. rewrite ?U2, ?U3, ?U4, ?U5, ?U6, ?UQ, ?UL1.
    clear P4 P5 GM D5. mod_small_inner.
    assert (E8 : (PGTOP - (usp + 8 * argc + 8 * envc)) / 8 = 512 * Q - 2 * s2 - (argc + envc)) by lia.
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_e_vis3n : uE E0 e_vis3n = 4096 * ((usp mod 32768) / 4096) + 4096 * Q.
  Proof.
    pose proof usp_decomp as (_ & D2 & _). pose proof PG_range as (_ & _ & _ & _ & _ & _ & QR). destruct uE0_PQ as [UP UQ]. unfold uE in *.
    unfold e_vis3n, eadd, escale. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit, u_add64, !u_mul64, !u64_lit by lia. rewrite UP, UQ.
    assert (HQ : 0 <= 4096 * Q < 2 ^ 64) by lia. assert (HP : 0 <= 4096 * (usp mod 32768 / 4096) < 2 ^ 64) by lia.
    rewrite (Z.mod_small _ _ HQ), (Z.mod_small _ _ HP). rewrite Z.mod_small by lia. reflexivity.
  Qed.
  Lemma u_e_top8 : uE E0 e_top8 = PGTOP / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & _). pose proof PG_range as (P1 & _ & P3 & _ & _ & P6 & QR).
    destruct uE0 as (U1 & _). destruct uE0_PQ as [UP UQ]. unfold uE in *.
    unfold e_top8, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U1, UP, UQ.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UQ.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. rewrite P6. unfold PGSP, pgdown. lia.
  Qed.
  Lemma u_e_top : uE E0 e_top = PGTOP.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & _). pose proof PG_range as (P1 & _ & P3 & _ & _ & P6 & QR).
    destruct uE0 as (U1 & _). destruct uE0_PQ as [UP UQ]. unfold uE in *.
    unfold e_top, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U1, UP, UQ.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UQ.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. rewrite P6. unfold PGSP, pgdown. lia.
  Qed.
  Lemma u_e_pgslack : uE E0 e_pgslack = PGTOP - (usp + Z.of_nat (length bsb)) + 200
                      /\ uE E0 e_pgslack8 = (PGTOP - (usp + Z.of_nat (length bsb)) + 200) / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3). pose proof bsb_ge as [G GM].
    pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P2 & P3 & P4 & P5 & P6 & QR).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). destruct uE0_PQ as [UP UQ]. unfold uE in *.
    unfold PGSP, pgdown in P1, P6.
    (* [comment removed for export] *)
    set (s1 := usp / 32768) in *. set (pp := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    clearbody s1 pp s2. first [clearbody Q | idtac]. first [clearbody PGTOP | idtac]. first [clearbody W | idtac]. first [clearbody PGSP | idtac].
    unfold e_pgslack, e_pgslack8, esub, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, ?mkAlu_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U2, U3, U4, U6, UQ.
    rewrite ?u_sub64, ?u_mul64, ?u_add64, ?u_mul64, ?u_add64. rewrite !u64_lit by lia. rewrite ?U2, ?U3, ?U4, ?U6, ?UQ.
    clear P4 P5 GM D5. mod_small_inner.
    split; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem ph sp argv envp uid hw rdraw.
  Definition model0 : Model := init_model (segments_reserved segs) brk0 mbase sp LIM inp.  (* [comment removed for export] *)

  Let cs0 := init_acs_of A.
  Let cs0z := init_acs_of_zero A.   (* [comment removed for export] *)
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (* [comment removed for export] *)
  Lemma alloc_top0 : alloc_top (m_vmmaps model0) = usp - 8388608.
  Proof. reflexivity. Qed.

  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIM /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite alloc_top0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  Lemma FULL0_below : forall a : word, usp - 8388608 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
    rdn segs Mr0 a n = rdn segs (stack_to_mem sp SIMG) a n.
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. unfold SIMG.
    rewrite <- (rdn_wrap_stack_above segs ph sp argv envp a n uid hw rdraw) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp in *; lia | apply Hvis; exact Hx].
  Qed.

  Lemma split_u : forall E e b k, split_lit e = (b, k) -> 0 <= k -> k <= uE E e ->
    bv_unsigned (edenot E b) + k = uE E e.
  Proof.
    intros E e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E e b k Hs) in Hle |- *.
    pose proof (u64_range (edenot E b)) as Rb.
    rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
    - rewrite Z.mod_small by lia. reflexivity.
    - exfalso.
      assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
      { replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      lia.
  Qed.

  Lemma adenot_SA : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ usp + 8 * argc + 8 * envc + 184 <= bv_unsigned a < usp + Z.of_nat (length bsb) - 16.
  Proof.
    intros a H. unfold argH0 in H. pose proof W_range as (W1 & W2 & W3).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 184)
     \/ usp + Z.of_nat (length bsb) - 16 <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kword_stack : forall b k v (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    rdn segs (stack_to_mem sp SIMG) w 8%nat = Some (word_le8 (edenot E0 v)) ->
    kentry_ok segs E0 Mr0 (KWord (SA b k) 8 v).
  Proof.
    hide_lets.
    intros b k v w Hw Hlo Hhi Hvis Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
    split; [exact Hfl|].
    rewrite adenot_SA. cbn [a_base a_off]. rewrite Hw, Z_to_bv_bv_unsigned.
    rewrite rdn_Mr0_stack; [| lia | change (Z.of_nat 8) with 8; lia | exact Hvis].
    rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
  Qed.

  Lemma spb_eq : split_lit e_sp0 = (e_sp0, 0).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 20)%nat ->
    nth j (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    hide_lets.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kword_stack ab (ak + 8 * Z.of_nat j) v (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold auxv_off, usp in *; [|lia].
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
    - rewrite <- Hv.
      pose proof (read_auxv_word segs ph sp rdraw argv envp uid hw Hva Hve Hhi' j Hj) as RW.
      exact RW.
  Qed.

  Lemma auxw_ok : forall i ty v,
    (0 <= i <= 9) ->
    nth (Z.to_nat (2 * i)) (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    hide_lets.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma Mr0_below : forall a : word, usp - 8388608 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | lia | apply not_argH0; lia].
  Qed.

  Lemma stack_window_ok :
    kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-8388608)) (ELit 8388608))
    /\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-8388608)) (ELit 8388608)).
  Proof.
    hide_lets.
    pose proof usp_lo. pose proof usp_hi.
    assert (Hst : estart E0 (SA e_sp0 (-8388608)) = usp - 8388608).
    { unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
    assert (Hl : elenZ E0 (ELit 8388608) = 8388608) by (apply elenZ_lit; lia).
    assert (Hfl : flat E0 (SA e_sp0 (-8388608)) (elenZ E0 (ELit 8388608))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
    - intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
  Qed.

  Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    hide_lets.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc ph segs sp argv envp uid hw rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3. unfold argc. exact (u_argcN argv Hva). }
      rewrite <- Hv. apply RW. fold bsb. pose proof usp_fit. unfold usp in *. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 e_str0).
  Proof.
    hide_lets.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp0 8 e_str0 (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k ph segs sp argv envp 0 uid hw rdraw Hav0) as RW.
      assert (Hv : cat_argv_ptr sp argv envp 0 = edenot E0 e_str0).
      { apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 0 Hav0).
        pose proof u_e_str0 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size. replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity.
        unfold usp, argc, envc. lia. }
      rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 e_argv1w).
  Proof.
    hide_lets.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 e_argv1w = if (1 <? argc) then edenot E0 e_str1 else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 e_str1)).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 e_argv1w (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k ph segs sp argv envp 1 uid hw rdraw Hav1) as RW.
        assert (Hv : cat_argv_ptr sp argv envp 1 = edenot E0 e_str1).
        { apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 1 Hav1).
          pose proof u_e_str1 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          rewrite Nat2Z.inj_add, (TF argv Hav0). unfold L0, usp, argc, envc. lia. }
        rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* [comment removed for export] *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
  Proof.
    hide_lets.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + Z.of_nat (length bsb) - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & Hrd)].
    fold bsb in Hlen.
    assert (Hu : bv_unsigned (at_random_ptr sp argv envp) = usp + Z.of_nat off).
    { rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
    rewrite (AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + Z.of_nat (length bsb) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
      replace (usp + Z.of_nat (length bsb) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma atrandom_zero_ok : kentry_ok segs E0 Mr0 (KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16)).
  Proof.
    hide_lets.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + Z.of_nat (length bsb) - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & Hrd)].
    fold bsb in Hlen.
    assert (Hu : bv_unsigned (at_random_ptr sp argv envp) = usp + Z.of_nat off).
    { rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
    pose proof Hzr as Hz0. unfold AsanCeil.zero_random_draw in Hz0.
    rewrite Hz0, AsanCeil.at_random_bytes_zero, repeat_firstn_skipn in Hrd by lia.
    assert (Ha : (at_random_ptr sp argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + Z.of_nat (length bsb) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
      replace (usp + Z.of_nat (length bsb) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
  Proof.
    pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    unfold Mr0, Mr, mrestrict. destruct (hid A argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
    apply FULL0_low. rewrite u64_lit; lia.
  Qed.

  Lemma rw_window_ok : kentry_ok segs E0 Mr0 (KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))).
  Proof.
    pose proof (if_rw _ _ _ IMG) as ((R1 & R0 & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  Lemma atr_ptr_eq : at_random_ptr sp argv envp = edenot E0 e_atrandom.
  Proof.
    pose proof usp_lo. pose proof usp_fit.
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & _)]. fold bsb in Hlen.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold usp. lia.
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    pose proof brk_range as [B1 B2]. pose proof bsb_ge as [G _]. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold init_kn_with.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (G1 & G2 & G3 & G4 & G5 & G6 & QR). destruct uE0_PQ as [UP UQ].
      unfold PGSP, pgdown in G1, G6.
      (* [comment removed for export] *)
      set (s1 := usp / 32768) in *. set (pp := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
      clearbody s1 pp s2. first [clearbody Q | idtac]. first [clearbody PGTOP | idtac]. first [clearbody PGSP | idtac]. first [clearbody W | idtac].
      clear D5.
      apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UP; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite UQ; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
      apply Forall_cons; [apply kr_ok; pose proof e_atr8m_range; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite (proj1 u_e_pgslack); lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite (proj2 u_e_pgslack); lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_top8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_top; lia|].
      pose proof u_e_blk as (UB1 & UB2 & UB3 & UB4 & UB5 & UB6). pose proof W8_ge as W8. pose proof L1_range as L1R.
      apply Forall_cons; [apply kr_ok; rewrite UB3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; change (uE E0 (EVar V_HW)) with (bv_unsigned hw); pose proof (u64_range hw); lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    1-10: apply auxw_ok; [lia | rewrite auxv_words_eq; cbn [nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; try reflexivity ..].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    1: exact atr_ptr_eq.
    apply Forall_cons; [exact Hatr|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    apply Forall_nil.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
  (* [comment removed for export] *)
  Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero A).
  Proof. exact (init_kn_with_ok _ atrandom_zero_ok). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma init_regs_nth : forall n, nth n init_regs (ELit 0) = if Nat.eqb n 2 then e_sp0 else ELit 0.
  Proof.
    intros n. unfold init_regs.
    do 32 (destruct n as [|n]; [reflexivity|]). cbn. destruct n; reflexivity.
  Qed.

  Lemma init_regs_ok : regs_ok E0 init_regs R0.
  Proof.
    hide_lets.
    intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
    - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
    - rewrite init_regs_nth. pose proof (ridx_range r) as Hlt.
      destruct (Nat.eqb (ridx r) 2) eqn:H2.
      + apply Nat.eqb_eq in H2. rewrite edenot_e_sp0.
        assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r); rewrite H2; apply bv_eq; reflexivity). subst r. reflexivity.
      + rewrite edenot_lit. apply Nat.eqb_neq in H2.
        rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
        set (n := ridx r) in *. clearbody n.
        do 32 (destruct n as [|n]; [first [exfalso; lia | vm_compute in Hr0 |- *; first [discriminate | reflexivity]] |]).
        exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_e_stkw : uE E0 (eaddz e_pgsp (-8388608)) = PGSP - 8388608
                   /\ uE E0 (eadd (ELit 8388608) (escale 16 (EVar V_S2))) = 8388608 + usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof u_e_pgsp as U. destruct uE0 as (_ & U2 & _).
    unfold uE in U, U2 |- *. unfold PGSP, pgdown. split.
    - unfold eaddz. rewrite mkAlu_denot, edenot_lit, u_add64.
      rewrite U. rewrite u_lit64. change ((-8388608) mod two64) with (two64 - 8388608). unfold two64.
      pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)). lia.
    - unfold eadd, escale. rewrite mkAlu_denot, mkMd_denot, !edenot_lit, u_add64, u_mul64, !u64_lit by lia. rewrite U2.
      rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_en_blk : uE E0 en_blk = Z.of_nat (length bsb).
  Proof.
    pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3). pose proof bsb_ge as [G _].
    destruct uE0 as (_ & _ & U3 & U4 & _ & U6 & _). unfold uE in U3, U4, U6 |- *.
    unfold en_blk, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, ?mkAlu_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U3, U4, U6.
    rewrite ?u_add64, ?u_mul64, ?u_add64, ?u_mul64, ?u_add64. rewrite ?U3, ?U4, ?U6. rewrite !u64_lit by lia.
    lia.
  Qed.

  (* [comment removed for export] *)
  Definition N2 : Z := 8388608 + usp mod 4096.
  Definition P3 : Z := 32768 * (usp / 32768).
  Definition N3 : Z := 4096 * ((usp mod 32768) / 4096) + 4096 * Q.
  Lemma PN3_range : usp - 32768 < P3 <= usp /\ P3 + N3 = PGTOP /\ 4096 <= N3 <= 32768 + 4096 * 600 /\ 8388608 <= N2 < 8388608 + 4096
                    /\ PGSP - 8388608 + N2 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P2 & P3' & P4 & P5 & P6 & QR). unfold P3, N3, N2.
    pose proof (Z.div_mod usp 32768 ltac:(lia)). pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)). pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)).
    unfold PGSP, pgdown in *. lia.
  Qed.
  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (PGSP - 8388608), pageup (PGSP - 8388608 + N2));
     (pagedown (shadow_off A + (PGSP - 8388608) / 8), pageup (shadow_off A + (PGSP - 8388608 + N2) / 8));
     (pagedown P3, pageup (P3 + N3));
     (pagedown (shadow_off A + P3 / 8), pageup (shadow_off A + (P3 + N3) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof u_e_stkw as [US UN2]. pose proof u_e_vis3b as UB. pose proof u_e_vis3n as UN. pose proof u_e_sp0 as USP.
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite US, UN2. rewrite UB, UN. fold N2. fold P3. fold N3.
    unfold uE. rewrite !edenot_lit, !u64_lit by lia. unfold N2. reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost 8392704 + vis_cost 4194304
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost 8392704 + vis_cost 4194304 <= LIM.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1. pose proof usp_lo as UL.
    pose proof PG_range as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & QR). pose proof PN3_range as (PR & PE & NR & NR2 & NE).
    rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost. pose proof HLIM as HL; unfold LIM_MIN in HL.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4). clear P1 P2.
    (* [comment removed for export] *)
    first [clearbody PGTOP | idtac]. first [clearbody Q | idtac]. first [clearbody W | idtac]. first [clearbody PGSP | idtac].
    clear - I1 I2 I3 I4 S1 UL Q3 PR PE NR NR2 NE HL.
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)) as M1.
    pose proof (pageup_minus_pagedown (PGSP - 8388608) (PGSP - 8388608 + N2) ltac:(lia)) as M2.
    pose proof (pageup_minus_pagedown (shadow_off A + (PGSP - 8388608) / 8) (shadow_off A + (PGSP - 8388608 + N2) / 8) ltac:(lia)) as M3.
    pose proof (pageup_minus_pagedown P3 (P3 + N3) ltac:(lia)) as M4.
    pose proof (pageup_minus_pagedown (shadow_off A + P3 / 8) (shadow_off A + (P3 + N3) / 8) ltac:(lia)) as M5.
    split; lia.
  Qed.

  Theorem init_cs_ok : cs_ok segs A LIM SINV0 argH0 usp fs E0 cs0 R0 FULL0 model0.   (* [comment removed for export] *)
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      unfold model0. apply init_sp_ok_init_model. exact Hsp.  (* [comment removed for export] *)
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.
    - constructor.   (* [comment removed for export] *)
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - (* [comment removed for export] *) split; [reflexivity | exact u_e_spw].
    - (* [comment removed for export] *) pose proof usp_lo. pose proof usp_fit. rewrite alloc_top0. unfold CEIL, TOPMAX. lia.
    - (* [comment removed for export] *) intros _; first [exact M7 | reflexivity].
    - (* [comment removed for export] *) intros iv Hiv _. rewrite ?M7 in Hiv. destruct Hiv.
    - (* [comment removed for export] *) rewrite ?M6. apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cs_ok_zero : cs_ok segs A LIM SINV0 argH0 usp fs E0 cs0z R0 FULL0 model0.   (* [comment removed for export] *)
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    change (allowA A E0 cs0) with (allowA A E0 (init_acs_of_zero A)) in AB1.   (* [comment removed for export] *)
    constructor; unfold cs0z; cbn [init_acs_of_zero init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_zero_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      unfold model0. apply init_sp_ok_init_model. exact Hsp.  (* [comment removed for export] *)
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.
    - constructor.   (* [comment removed for export] *)
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - (* [comment removed for export] *) split; [reflexivity | exact u_e_spw].
    - (* [comment removed for export] *) pose proof usp_lo. pose proof usp_fit. rewrite alloc_top0. unfold CEIL, TOPMAX. lia.
    - (* [comment removed for export] *) intros _; first [exact M7 | reflexivity].
    - (* [comment removed for export] *) intros iv Hiv _. rewrite ?M7 in Hiv. destruct Hiv.
    - (* [comment removed for export] *) rewrite ?M6. apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cfg_eq : forall apc : N, Z.of_N apc = a_entry A ->
    init_config segs apc ph sp brk0 mbase rdraw LIM inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof.
    intros apc Hpc. unfold init_config, cfg_of. cbn [in_argv in_envp in_uid in_hwcap inp]. rewrite init_mkst. rewrite Hpc. reflexivity.
  Qed.
End Init.
