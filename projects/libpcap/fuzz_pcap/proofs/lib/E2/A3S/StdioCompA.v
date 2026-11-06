(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Ox.F64_007.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase AMalloc_iface RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import GIA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA Stdio_glueKitA I_ahm I_fflush. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioLawsA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section StdioComp.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {hptr : Type}.
  #[local] Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stdio_files_dom (FB : list cblk) (a : Z) : Prop := stdio_static a \/ in_block FB a.

  #[using="Type"] Lemma STDIOR_agree_dom : forall (l : libc_st hptr) FB m m',
    STDIOR l FB m -> agrees_on (stdio_files_dom FB) m m' -> STDIOR l FB m'.
  Proof.
    intros l FB m m' SR AG. eapply (STDIOR_agree l FB m m' (stdio_files_dom FB)); [exact SR | exact AG | |].
    - intros a Ha. left. exact Ha.
    - intros a Ha. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Definition stdio_blob1 : list cell :=
    file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDIO_WRITE F_STDIO_SEEK A_STDERR_BUF 0 0 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)
    ++ [C8 (Z_to_bv 64 A_STDERR)]
    ++ stdin_cells
    ++ [C8 (Z_to_bv 64 A_STDIN)]
    ++ file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDOUT_WRITE F_STDIO_SEEK A_STDOUT_BUF 1024 0 0 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)
    ++ [C8 (Z_to_bv 64 A_STDOUT)].
  Definition stdio_blob2 : list cell :=
    [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); CB 8 (repeat (Z_to_bv 8 0) 8)]
    ++ [CB 0 []]
    ++ [CB 8 (repeat (Z_to_bv 8 0) 8); CB 1024 (repeat (Z_to_bv 8 0) 1024); CB 8 (repeat (Z_to_bv 8 0) 8)]
    ++ [CB 1024 (repeat (Z_to_bv 8 0) 1024)].

  #[using="Type"] Lemma stdio_blob1_wf : cells_wf stdio_blob1 /\ cells_size stdio_blob1 = 720%nat.
  Proof. split; [vm_compute; repeat split; exact I | vm_compute; reflexivity]. Qed.
  #[using="Type"] Lemma stdio_blob2_wf : cells_wf stdio_blob2 /\ cells_size stdio_blob2 = 2088%nat.
  Proof. split; [vm_compute; repeat split; exact I | vm_compute; reflexivity]. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma stdio_blob1_img : rw_bytes_b asegs 0xa9ab0 (cells_bytes stdio_blob1) = true.
  Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma stdio_blob2_img : rw_bytes_b asegs 0x601ca8 (cells_bytes stdio_blob2) = true.
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem stdio_initA : stdio_init_stmt (hptr := hptr).
  Proof.
    unfold stdio_init_stmt. intros m SO SE SI [bb SOB] SEB U1 U2 U3 OL OH.
    unfold STDIOR, libc_init. cbn [lc_stdout lc_stderr lc_files hd_addr files_R map].
    split.
    { exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), bb.
      split; [unfold fcells; cbn; exact SO|].
      split; [unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM; cbn; repeat split; reflexivity|].
      split; [cbn; exact SOB|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [cbn [f_wbuf f_bufsize stdout_init]; unfold zlength, BUFSIZ; cbn [length Z.of_nat]; lia|].
      split; [intros H; exfalso; exact (H eq_refl)|]. cbn [f_rbuf stdout_init stderr_init]; unfold zlength; cbn [length Z.of_nat]. split; [lia| split; [lia| reflexivity]]. }
    split; [unfold stdout_inv; cbn; repeat split; reflexivity|].
    split.
    { exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), [].
      split; [unfold fcells; cbn; exact SE|].
      split; [unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM; cbn; repeat split; reflexivity|].
      split; [cbn; exact SEB|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [cbn [f_wbuf f_bufsize stderr_init]; unfold zlength; cbn [length Z.of_nat]; lia|].
      split; [intros H; exfalso; exact (H eq_refl)|]. cbn [f_rbuf stdout_init stderr_init]; unfold zlength; cbn [length Z.of_nat]. split; [lia| split; [lia| reflexivity]]. }
    split; [unfold stderr_inv; cbn; repeat split; reflexivity|].
    split; [exact SI|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact OL|]. split; [exact OH|].
    split; [exact I|]. constructor.
  Qed.

  #[using="Type"] Theorem stdio_files_initA : forall m,
    rw_cells asegs m 0xa9ab0 stdio_blob1 -> rw_cells asegs m 0x601ca8 stdio_blob2 -> STDIOR (@libc_init hptr) [] m.
  Proof.
    intros m B1 B2. unfold stdio_blob1 in B1. unfold stdio_blob2 in B2.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B1 as [SE B1]. rewrite file_cells_size in B1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in B1.
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in B1 as [UE B1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B1 as [SI B1]. unfold stdin_cells in B1 at 1. rewrite file_cells_size in B1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1.
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in B1 as [UI B1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B1 as [SO UO]. rewrite file_cells_size in UO. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in UO.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B2 as [OFL B2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B2.
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in B2 as [EB B2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B2.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B2 as [IB OB]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in OB.
    apply (proj1 (rw_cells_app asegs m _ [_;_] _)) in OFL as [OL OH]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in OH.
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in OL as [OL _].
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in OH as [OH _].
    eapply stdio_initA; unfold A_STDOUT, A_STDERR, A_STDIN, A_STDOUT_BUF, A_STDERR_BUF, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD;
      first [exact SO | exact SE | exact SI | (eexists; exact OB) | exact EB | exact UE | exact UI | exact UO | exact OL | exact OH
            | match goal with |- ?g => idtac "INITLEFT:" g end].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition STDIO_ENV_CELLS : list (Z * Z) :=
    [(0xa71e8, 0xa71f8); (0xa7218, 0xa7220); (0xa7248, 0xa7250); (0xa7268, 0xa7278); (0xa7290, 0xa72a8); (0xade40, 0xade50); (0x6015f8, 0x601600);
     (0x601849, 0x60184a); (0x60184b, 0x60184c)].   (* [comment removed for export] *)
  Definition stdio_env_dom (a : Z) : Prop :=
    in_ranges STDIO_ENV_CELLS a \/ (AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN) \/ (AAHMv <= a < AAHMv + AAHM_SZ).

  (* [comment removed for export] *)
  Definition stdio_env_P (can : word) (RNG : footprint) (m : mem) : Prop :=
    (rt_real_strchr m /\ rt_real_strrchr m /\ rt_real_fread m /\ rt_real_vsnprintf m /\ rt_real_strerror m /\ rt_real_fopen m)
    /\ (rw_cells asegs m ssp_guard [C8 can]
        /\ rw_cells asegs m 0x601849 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x60184b [C1 (Z_to_bv 8 0)])   (* [comment removed for export] *)
    /\ (rt_ahm m AAHMv /\ ahm_zero m AAHMv /\ AAHMv mod 8 = 0 /\ 0x603000 <= AAHMv /\ AAHMv + AHM_BYTES <= ATOP /\ rng RNG AAHMv AHM_BYTES)
    /\ (unpoisoned m 0x10000 0x21000 /\ unpoisoned m 0x22ca0 0x32000 /\ unpoisoned m 0xa9ab0 0xa9d80 /\ unpoisoned m 0x601ca8 0x6024d0)
    /\ rng0 RNG.

  Local Ltac in_env_cell := left; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; repeat (first [left; reflexivity | right]) | cbn [fst snd]; lia].

  #[using="Type"] Lemma stdio_env_agree : forall can RNG RNG' m m',
    stdio_env_P can RNG m -> fp_le RNG RNG' -> agrees_on stdio_env_dom m m' -> stdio_env_P can RNG' m'.
  Proof.
    intros can RNG RNG' m m' ((C1 & C2 & C3 & C4 & C5 & C6) & (CAN & THR & NLK) & (AH1 & AH2 & AH3 & AH4 & AH5 & AH6) & (U1 & U2 & U3 & U4) & R0) FP AG.
    assert (KC : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_ranges STDIO_ENV_CELLS a) -> rw_cells asegs m' A cs).
    { intros A cs HC HR. eapply agrees_rw_cells; [exact AG | exact HC |]. intros a Ha. left. apply HR. exact Ha. }
    assert (KU : forall lo hi, unpoisoned m lo hi -> 0x10000 <= lo -> hi <= 0x603000 -> lo < hi -> unpoisoned m' lo hi).
    { intros lo hi U HL HH LT. eapply unpoisoned_agree; [exact U|]. intros sa Hs. rewrite !shad_div in Hs. unfold ASHOFF in Hs.
      apply AG; [clear - Hs HL HH LT; Z.div_mod_to_equations; lia|].
      right; left. unfold AIMSH_LO, AIMSH_LEN. clear - Hs HL HH LT. Z.div_mod_to_equations. lia. }
    split.
    { split; [apply (KC _ _ C1); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; left; reflexivity | cbn [fst snd]; lia]|].
      split; [apply (KC _ _ C2); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; left; reflexivity | cbn [fst snd]; lia]|].
      split; [apply (KC _ _ C3); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; right; left; reflexivity | cbn [fst snd]; lia]|].
      split; [apply (KC _ _ C4); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; right; right; left; reflexivity | cbn [fst snd]; lia]|].
      split; [apply (KC _ _ C5); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; right; right; right; left; reflexivity | cbn [fst snd]; lia]|].
      apply (KC _ _ C6); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; right; right; right; right; left; reflexivity | cbn [fst snd]; lia]. }
    split.
    { split; [| split].
      - apply (KC _ _ CAN). unfold ssp_guard. cbn [cells_size csize Nat.add]. intros a Ha.
        eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; do 6 right; left; reflexivity | cbn [fst snd]; lia].
      - apply (KC _ _ THR). cbn [cells_size csize Nat.add]. intros a Ha.
        eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; do 7 right; left; reflexivity | cbn [fst snd]; lia].
      - apply (KC _ _ NLK). cbn [cells_size csize Nat.add]. intros a Ha.
        eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; do 8 right; left; reflexivity | cbn [fst snd]; lia]. }
    split.
    { split; [apply (KC _ _ AH1); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; do 5 right; left; reflexivity | cbn [fst snd]; lia]|].
      split.
      { destruct AH2 as [WR Z0]. unfold AHM_BYTES, AAHM_SZ in *. split.
        - eapply agrees_wr_at; [exact AG | exact WR |]. intros a Ha. right; right. unfold AAHM_SZ, AHM_BYTES in *. clear - Ha. lia.
        - intros i Hi. rewrite <- (Z0 i Hi). unfold mrd.
          destruct WR as (T0 & THI & _).
          assert (IR : 0 <= AAHMv + i < 2^64 /\ AAHMv <= AAHMv + i < AAHMv + AAHM_SZ) by (unfold AAHM_SZ, AHM_BYTES in *; clear - Hi T0 THI; lia).
          destruct (AG (AAHMv + i) (proj1 IR) ltac:(right; right; exact (proj2 IR))) as [E _]. rewrite E. reflexivity. }
      split; [exact AH3|]. split; [exact AH4|]. split; [exact AH5|]. exact (rng_fp_le _ _ _ _ FP AH6). }
    split.
    { split; [apply (KU _ _ U1); lia|]. split; [apply (KU _ _ U2); lia|]. split; [apply (KU _ _ U3); lia| apply (KU _ _ U4); lia]. }
    intros b Hb. exact (rng_fp_le _ _ _ _ FP (R0 b Hb)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma stdio_env_icptenv : forall can RNG m,
    stdio_env_P can RNG m -> rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m -> rt_real_read m -> rt_real_printf m ->
    rt_real_strlen m -> rt_real_memchr m -> rt_real_fwrite m -> rt_real_strnlen m -> rt_isl m -> rt_ssc m -> icptenv m.
  Proof.
    intros can RNG m ((C1 & C2 & C3 & C4 & C5 & C6) & _) G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14.
    constructor; assumption.
  Qed.

  #[using="Type"] Lemma stdio_env_ssp : forall can RNG m,
    stdio_env_P can RNG m -> rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> ssp_cells m can.
  Proof. intros can RNG m (_ & (CAN & _) & _) GOT. split; [exact GOT | exact CAN]. Qed.

  #[using="Type"] Lemma stdio_env_libc : forall can RNG m, stdio_env_P can RNG m ->
    rw_cells asegs m 0x601849 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x60184b [C1 (Z_to_bv 8 0)].
  Proof. intros can RNG m (_ & (_ & THR & NLK) & _). split; [exact THR | exact NLK]. Qed.

  #[using="Type"] Lemma stdio_env_ahm : forall can RNG m, stdio_env_P can RNG m ->
    exists T, rt_ahm m T /\ T mod 8 = 0 /\ 0x603000 <= T /\ T + AHM_BYTES <= ATOP /\ rng RNG T AHM_BYTES /\ ahm_zero m T.
  Proof.
    intros can RNG m (_ & _ & (AH1 & AH2 & AH3 & AH4 & AH5 & AH6) & _). exists AAHMv.
    split; [exact AH1|]. split; [exact AH3|]. split; [exact AH4|]. split; [exact AH5|]. split; [exact AH6 | exact AH2].
  Qed.

  #[using="Type"] Lemma stdio_env_rng0 : forall can RNG m, stdio_env_P can RNG m -> rng0 RNG.
  Proof. intros can RNG m (_ & _ & _ & _ & R0). exact R0. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma static_sobj : forall RNG m A B, unpoisoned m A B -> 0x10040 <= A -> A <= B -> B <= 0x602fc0 ->
    wr_at asegs m 0x7fffa000 779776 -> rng_aimg RNG -> rng RNG 0x7fffa000 779776 -> sobj RNG m A B.
  Proof.
    intros RNG m A B U HA HAB HB W RI RS.
    replace B with (A + (B - A)) by lia. apply mobjA_sobj; [| lia].
    apply static_mobjA; [exact HA | lia | lia | replace (A + (B - A)) with B by lia; exact U | exact W | exact RI | exact RS].
  Qed.

  #[using="Type"] Lemma stdio_env_statics : forall can RNG m,
    stdio_env_P can RNG m -> wr_at asegs m 0x7fffa000 779776 -> rng_aimg RNG -> rng RNG 0x7fffa000 779776 ->
    sobj RNG m 0xa9ab0 0xa9d80 /\ sobj RNG m 0x601ca8 0x6024d0.
  Proof.
    intros can RNG m (_ & _ & _ & (U1 & U2 & U3 & U4) & _) W RI RS.
    split; (apply static_sobj; [assumption | lia | lia | lia | exact W | exact RI | exact RS]).
  Qed.

  #[using="Type"] Lemma stdio_env_rodata : forall can RNG m lo hi,
    stdio_env_P can RNG m -> wr_at asegs m 0x7fffa000 779776 -> rng_aimg RNG -> rng RNG 0x7fffa000 779776 ->
    (0x10040 <= lo /\ hi <= 0x21000) \/ (0x22ca0 <= lo /\ hi <= 0x32000) -> lo <= hi -> sobj RNG m lo hi.
  Proof.
    intros can RNG m lo hi (_ & _ & _ & (U1 & U2 & U3 & U4) & _) W RI RS HR LE.
    destruct HR as [[H1 H2]|[H1 H2]].
    - apply static_sobj; [eapply unpoisoned_sub; [exact U1 | lia | lia] | lia | lia | lia | exact W | exact RI | exact RS].
    - apply static_sobj; [eapply unpoisoned_sub; [exact U2 | lia | lia] | lia | lia | lia | exact W | exact RI | exact RS].
  Qed.
End StdioComp.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section StdioComp.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {hptr : Type}.
  #[local] Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stdio_files_dom (FB : list cblk) (a : Z) : Prop := stdio_static a \/ in_block FB a.

  #[using="Type"] Lemma STDIOR_agree_dom : forall (l : libc_st hptr) FB m m',
    STDIOR l FB m -> agrees_on (stdio_files_dom FB) m m' -> STDIOR l FB m'.
  Proof.
    intros l FB m m' SR AG. eapply (STDIOR_agree l FB m m' (stdio_files_dom FB)); [exact SR | exact AG | |].
    - intros a Ha. left. exact Ha.
    - intros a Ha. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Definition stdio_blob1 : list cell :=
    file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDIO_WRITE F_STDIO_SEEK A_STDERR_BUF 0 0 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)
    ++ [C8 (Z_to_bv 64 A_STDERR)]
    ++ stdin_cells
    ++ [C8 (Z_to_bv 64 A_STDIN)]
    ++ file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDOUT_WRITE F_STDIO_SEEK A_STDOUT_BUF 1024 0 0 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)
    ++ [C8 (Z_to_bv 64 A_STDOUT)].
  Definition stdio_blob2 : list cell :=
    [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); CB 8 (repeat (Z_to_bv 8 0) 8)]
    ++ [CB 0 []]
    ++ [CB 8 (repeat (Z_to_bv 8 0) 8); CB 1024 (repeat (Z_to_bv 8 0) 1024); CB 8 (repeat (Z_to_bv 8 0) 8)]
    ++ [CB 1024 (repeat (Z_to_bv 8 0) 1024)].

  #[using="Type"] Lemma stdio_blob1_wf : cells_wf stdio_blob1 /\ cells_size stdio_blob1 = 720%nat.
  Proof. split; [vm_compute; repeat split; exact I | vm_compute; reflexivity]. Qed.
  #[using="Type"] Lemma stdio_blob2_wf : cells_wf stdio_blob2 /\ cells_size stdio_blob2 = 2088%nat.
  Proof. split; [vm_compute; repeat split; exact I | vm_compute; reflexivity]. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma stdio_blob1_img : rw_bytes_b asegs 0xa9e90 (cells_bytes stdio_blob1) = true.
  Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma stdio_blob2_img : rw_bytes_b asegs 0x6020a8 (cells_bytes stdio_blob2) = true.
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem stdio_initA : stdio_init_stmt (hptr := hptr).
  Proof.
    unfold stdio_init_stmt. intros m SO SE SI [bb SOB] SEB U1 U2 U3 OL OH.
    unfold STDIOR, libc_init. cbn [lc_stdout lc_stderr lc_files hd_addr files_R map].
    split.
    { exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), bb.
      split; [unfold fcells; cbn; exact SO|].
      split; [unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM; cbn; repeat split; reflexivity|].
      split; [cbn; exact SOB|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [cbn [f_wbuf f_bufsize stdout_init]; unfold zlength, BUFSIZ; cbn [length Z.of_nat]; lia|].
      split; [intros H; exfalso; exact (H eq_refl)|]. cbn [f_rbuf stdout_init stderr_init]; unfold zlength; cbn [length Z.of_nat]. split; [lia| split; [lia| reflexivity]]. }
    split; [unfold stdout_inv; cbn; repeat split; reflexivity|].
    split.
    { exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), [].
      split; [unfold fcells; cbn; exact SE|].
      split; [unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM; cbn; repeat split; reflexivity|].
      split; [cbn; exact SEB|]. split; [reflexivity|]. split; [intros _; reflexivity|]. split; [cbn [f_wbuf f_bufsize stderr_init]; unfold zlength; cbn [length Z.of_nat]; lia|].
      split; [intros H; exfalso; exact (H eq_refl)|]. cbn [f_rbuf stdout_init stderr_init]; unfold zlength; cbn [length Z.of_nat]. split; [lia| split; [lia| reflexivity]]. }
    split; [unfold stderr_inv; cbn; repeat split; reflexivity|].
    split; [exact SI|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact OL|]. split; [exact OH|].
    split; [exact I|]. constructor.
  Qed.

  #[using="Type"] Theorem stdio_files_initA : forall m,
    rw_cells asegs m 0xa9e90 stdio_blob1 -> rw_cells asegs m 0x6020a8 stdio_blob2 -> STDIOR (@libc_init hptr) [] m.
  Proof.
    intros m B1 B2. unfold stdio_blob1 in B1. unfold stdio_blob2 in B2.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B1 as [SE B1]. rewrite file_cells_size in B1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in B1.
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in B1 as [UE B1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B1 as [SI B1]. unfold stdin_cells in B1 at 1. rewrite file_cells_size in B1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1.
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in B1 as [UI B1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B1 as [SO UO]. rewrite file_cells_size in UO. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in UO.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B2 as [OFL B2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B2.
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in B2 as [EB B2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B2.
    apply (proj1 (rw_cells_app asegs m _ _ _)) in B2 as [IB OB]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in OB.
    apply (proj1 (rw_cells_app asegs m _ [_;_] _)) in OFL as [OL OH]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in OH.
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in OL as [OL _].
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in OH as [OH _].
    eapply stdio_initA; unfold A_STDOUT, A_STDERR, A_STDIN, A_STDOUT_BUF, A_STDERR_BUF, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD;
      first [exact SO | exact SE | exact SI | (eexists; exact OB) | exact EB | exact UE | exact UI | exact UO | exact OL | exact OH
            | match goal with |- ?g => idtac "INITLEFT:" g end].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition STDIO_ENV_CELLS : list (Z * Z) :=
    [(0xa75c8, 0xa75d8); (0xa75f8, 0xa7600); (0xa7628, 0xa7630); (0xa7648, 0xa7658); (0xa7670, 0xa7688); (0xae240, 0xae250); (0x6019f8, 0x601a00);
     (0x601c49, 0x601c4a); (0x601c4b, 0x601c4c)].   (* [comment removed for export] *)
  Definition stdio_env_dom (a : Z) : Prop :=
    in_ranges STDIO_ENV_CELLS a \/ (AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN) \/ (AAHMv <= a < AAHMv + AAHM_SZ).

  (* [comment removed for export] *)
  Definition stdio_env_P (can : word) (RNG : footprint) (m : mem) : Prop :=
    (rt_real_strchr m /\ rt_real_strrchr m /\ rt_real_fread m /\ rt_real_vsnprintf m /\ rt_real_strerror m /\ rt_real_fopen m)
    /\ (rw_cells asegs m ssp_guard [C8 can]
        /\ rw_cells asegs m 0x601c49 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x601c4b [C1 (Z_to_bv 8 0)])   (* [comment removed for export] *)
    /\ (rt_ahm m AAHMv /\ ahm_zero m AAHMv /\ AAHMv mod 8 = 0 /\ 0x604000 <= AAHMv /\ AAHMv + AHM_BYTES <= ATOP /\ rng RNG AAHMv AHM_BYTES)
    /\ (unpoisoned m 0x10000 0x21000 /\ unpoisoned m 0x22ca0 0x32000 /\ unpoisoned m 0xa9e90 0xaa160 /\ unpoisoned m 0x6020a8 0x6028d0)
    /\ rng0 RNG.

  Local Ltac in_env_cell := left; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; repeat (first [left; reflexivity | right]) | cbn [fst snd]; lia].

  #[using="Type"] Lemma stdio_env_agree : forall can RNG RNG' m m',
    stdio_env_P can RNG m -> fp_le RNG RNG' -> agrees_on stdio_env_dom m m' -> stdio_env_P can RNG' m'.
  Proof.
    intros can RNG RNG' m m' ((C1 & C2 & C3 & C4 & C5 & C6) & (CAN & THR & NLK) & (AH1 & AH2 & AH3 & AH4 & AH5 & AH6) & (U1 & U2 & U3 & U4) & R0) FP AG.
    assert (KC : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_ranges STDIO_ENV_CELLS a) -> rw_cells asegs m' A cs).
    { intros A cs HC HR. eapply agrees_rw_cells; [exact AG | exact HC |]. intros a Ha. left. apply HR. exact Ha. }
    assert (KU : forall lo hi, unpoisoned m lo hi -> 0x10000 <= lo -> hi <= 0x604000 -> lo < hi -> unpoisoned m' lo hi).
    { intros lo hi U HL HH LT. eapply unpoisoned_agree; [exact U|]. intros sa Hs. rewrite !shad_div in Hs. unfold ASHOFF in Hs.
      apply AG; [clear - Hs HL HH LT; Z.div_mod_to_equations; lia|].
      right; left. unfold AIMSH_LO, AIMSH_LEN. clear - Hs HL HH LT. Z.div_mod_to_equations. lia. }
    split.
    { split; [apply (KC _ _ C1); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; left; reflexivity | cbn [fst snd]; lia]|].
      split; [apply (KC _ _ C2); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; left; reflexivity | cbn [fst snd]; lia]|].
      split; [apply (KC _ _ C3); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; right; left; reflexivity | cbn [fst snd]; lia]|].
      split; [apply (KC _ _ C4); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; right; right; left; reflexivity | cbn [fst snd]; lia]|].
      split; [apply (KC _ _ C5); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; right; right; right; left; reflexivity | cbn [fst snd]; lia]|].
      apply (KC _ _ C6); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; right; right; right; right; left; reflexivity | cbn [fst snd]; lia]. }
    split.
    { split; [| split].
      - apply (KC _ _ CAN). unfold ssp_guard. cbn [cells_size csize Nat.add]. intros a Ha.
        eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; do 6 right; left; reflexivity | cbn [fst snd]; lia].
      - apply (KC _ _ THR). cbn [cells_size csize Nat.add]. intros a Ha.
        eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; do 7 right; left; reflexivity | cbn [fst snd]; lia].
      - apply (KC _ _ NLK). cbn [cells_size csize Nat.add]. intros a Ha.
        eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; do 8 right; left; reflexivity | cbn [fst snd]; lia]. }
    split.
    { split; [apply (KC _ _ AH1); cbn [cells_size csize Nat.add]; intros a Ha; eexists; split; [unfold STDIO_ENV_CELLS; cbn [In]; do 5 right; left; reflexivity | cbn [fst snd]; lia]|].
      split.
      { destruct AH2 as [WR Z0]. unfold AHM_BYTES, AAHM_SZ in *. split.
        - eapply agrees_wr_at; [exact AG | exact WR |]. intros a Ha. right; right. unfold AAHM_SZ, AHM_BYTES in *. clear - Ha. lia.
        - intros i Hi. rewrite <- (Z0 i Hi). unfold mrd.
          destruct WR as (T0 & THI & _).
          assert (IR : 0 <= AAHMv + i < 2^64 /\ AAHMv <= AAHMv + i < AAHMv + AAHM_SZ) by (unfold AAHM_SZ, AHM_BYTES in *; clear - Hi T0 THI; lia).
          destruct (AG (AAHMv + i) (proj1 IR) ltac:(right; right; exact (proj2 IR))) as [E _]. rewrite E. reflexivity. }
      split; [exact AH3|]. split; [exact AH4|]. split; [exact AH5|]. exact (rng_fp_le _ _ _ _ FP AH6). }
    split.
    { split; [apply (KU _ _ U1); lia|]. split; [apply (KU _ _ U2); lia|]. split; [apply (KU _ _ U3); lia| apply (KU _ _ U4); lia]. }
    intros b Hb. exact (rng_fp_le _ _ _ _ FP (R0 b Hb)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma stdio_env_icptenv : forall can RNG m,
    stdio_env_P can RNG m -> rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m -> rt_real_read m -> rt_real_printf m ->
    rt_real_strlen m -> rt_real_memchr m -> rt_real_fwrite m -> rt_real_strnlen m -> rt_isl m -> rt_ssc m -> icptenv m.
  Proof.
    intros can RNG m ((C1 & C2 & C3 & C4 & C5 & C6) & _) G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14.
    constructor; assumption.
  Qed.

  #[using="Type"] Lemma stdio_env_ssp : forall can RNG m,
    stdio_env_P can RNG m -> rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> ssp_cells m can.
  Proof. intros can RNG m (_ & (CAN & _) & _) GOT. split; [exact GOT | exact CAN]. Qed.

  #[using="Type"] Lemma stdio_env_libc : forall can RNG m, stdio_env_P can RNG m ->
    rw_cells asegs m 0x601c49 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m 0x601c4b [C1 (Z_to_bv 8 0)].
  Proof. intros can RNG m (_ & (_ & THR & NLK) & _). split; [exact THR | exact NLK]. Qed.

  #[using="Type"] Lemma stdio_env_ahm : forall can RNG m, stdio_env_P can RNG m ->
    exists T, rt_ahm m T /\ T mod 8 = 0 /\ 0x604000 <= T /\ T + AHM_BYTES <= ATOP /\ rng RNG T AHM_BYTES /\ ahm_zero m T.
  Proof.
    intros can RNG m (_ & _ & (AH1 & AH2 & AH3 & AH4 & AH5 & AH6) & _). exists AAHMv.
    split; [exact AH1|]. split; [exact AH3|]. split; [exact AH4|]. split; [exact AH5|]. split; [exact AH6 | exact AH2].
  Qed.

  #[using="Type"] Lemma stdio_env_rng0 : forall can RNG m, stdio_env_P can RNG m -> rng0 RNG.
  Proof. intros can RNG m (_ & _ & _ & _ & R0). exact R0. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma static_sobj : forall RNG m A B, unpoisoned m A B -> 0x10040 <= A -> A <= B -> B <= 0x603fc0 ->
    wr_at asegs m 0x7fffa000 780288 -> rng_aimg RNG -> rng RNG 0x7fffa000 780288 -> sobj RNG m A B.
  Proof.
    intros RNG m A B U HA HAB HB W RI RS.
    replace B with (A + (B - A)) by lia. apply mobjA_sobj; [| lia].
    apply static_mobjA; [exact HA | lia | lia | replace (A + (B - A)) with B by lia; exact U | exact W | exact RI | exact RS].
  Qed.

  #[using="Type"] Lemma stdio_env_statics : forall can RNG m,
    stdio_env_P can RNG m -> wr_at asegs m 0x7fffa000 780288 -> rng_aimg RNG -> rng RNG 0x7fffa000 780288 ->
    sobj RNG m 0xa9e90 0xaa160 /\ sobj RNG m 0x6020a8 0x6028d0.
  Proof.
    intros can RNG m (_ & _ & _ & (U1 & U2 & U3 & U4) & _) W RI RS.
    split; (apply static_sobj; [assumption | lia | lia | lia | exact W | exact RI | exact RS]).
  Qed.

  #[using="Type"] Lemma stdio_env_rodata : forall can RNG m lo hi,
    stdio_env_P can RNG m -> wr_at asegs m 0x7fffa000 780288 -> rng_aimg RNG -> rng RNG 0x7fffa000 780288 ->
    (0x10040 <= lo /\ hi <= 0x21000) \/ (0x22ca0 <= lo /\ hi <= 0x32000) -> lo <= hi -> sobj RNG m lo hi.
  Proof.
    intros can RNG m lo hi (_ & _ & _ & (U1 & U2 & U3 & U4) & _) W RI RS HR LE.
    destruct HR as [[H1 H2]|[H1 H2]].
    - apply static_sobj; [eapply unpoisoned_sub; [exact U1 | lia | lia] | lia | lia | lia | exact W | exact RI | exact RS].
    - apply static_sobj; [eapply unpoisoned_sub; [exact U2 | lia | lia] | lia | lia | lia | exact W | exact RI | exact RS].
  Qed.
End StdioComp.
End TwB.
