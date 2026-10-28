(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase AQConst ABytes ARepQ.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AKit AKit2 AKitQ F_amerge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_aqrec_iface () := "C47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00I35stdpp4base5NoDup00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00c5ARocqVerifyHarness?AgentSubmission5BothW=F_aqrec_iface6deq_bqI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=dequeue_whileC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6b_sizeK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3subI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6abatch00I47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ7qbatchc00C5ARocqVerifyHarness?AgentSubmission5BothW8F_amerge2bqI47Corelib4Init9Datatypes4bool00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Fixpoint deq_bq (l : list bq) (bytes min_size : Z) {struct l} : list bq * list bq * Z :=
  match l with
  | [] => ([], [], bytes)
  | b :: l' => if min_size <? bytes
               then let '(taken, rest, bytes') := deq_bq l' (bytes - b_size (fst b)) min_size in (b :: taken, rest, bytes')
               else ([], l, bytes)
  end.

Lemma deq_bq_fst : forall l bytes min_size,
  let '(taken, rest, bytes') := deq_bq l bytes min_size in
  dequeue_while (map fst l) bytes min_size = (map fst taken, map fst rest, bytes').
Proof.
ltac2:(KReplay.run1 (kr_t_F_aqrec_iface ()) ["CANSEC1"] "p'0h02IHh15bytesh21li001lh38min_sizeh41pi011ph51bi021bh62b0h72b2h82rsh92tkh:1zi031zi046bytes'i054resti065takeni071xp;1p;2p;3p;6p;5p;4p-1R0g0000R1p4p710p8P0P1p4p7210p8P0p1000Lp4p710p8P0g000mR2p4p710p8P0P2p4p7210p8P0p1001JR3p4p710R4p8P0P3p4p7210R3p8P0p1001^p4p710R0p8p1002:p4p710R5P4p8P5P3p8P5P0p8g002Oj1@Tg002oR0j28Tg003Oj37TP2j2Cj3DTg004Nj32Tg004hj1<Tg005Hj2;Tg005bj3:Tg006bj2BTg007?j1ATg0088j39Tg008Xj6FTg0096j5ETP1j4?Tg009Xj4=Tg00:8j2>Tf4R1g00:UR2f3R5f2R3C?f1R4f0R63:p=4P3P2P4P6C?p=5f5R7g00;PR8P1P5P3P4C=P6C=p=0g00;nR9=D26p=1%A6,>4p=6g00<hR:?946p=31>34=:56p=G%@:R;P:P018;;R<P8p-0R=A7346P0P;P;P=P4%@2R>/8>R?/88R@1829RA1C29R9f6RBP7P1D4P?P>P>A5A94RCA5A96P3E0RD32n2001101000120106105n2001107000120101104^38^18REX2;P?P>P>%<2RFPFP4E0,;@P0P<P8P=%<:RG?746P0P;P;P=P4A5A9GRH?:71=2@Dn2001101000120106105n2001107000120101104eX38X181B64g00=^RIPIP0P<P8P=PI18<8RJP6P0P<P8PJ%1B,65=773RKP0P;P;PJP4P<P;P;f:RL/34P6P3E0n2001101000120106105n2001107000120101104P<P;P;PG13B7P5E0n0100000020000P0P;P;P=P4PIP@P1P0P?P8P@f9RI95A9RGf7RM%1LRN#APBCGP0P>P>P@P4P?P>P>f>RO#1RP=924P6P3E0n2001101000120106105n2001107000120101104P?P>P>PFA92NGPME0n0100000020000=2@Dn2001101000120106105n2001107000120101104P6P5%17,63RNP4O2P0P<P8P=A71N4P0P;P;P=P4PAP9f8RN%1I,6BP7D4=2@Dn2001101000120106105n2001107000120101104PKPJP0P<P8P0P<P8P=P6P0P;P;P=P4PAP9f;RKf<RB#1,6IPND4=2@Dn2001101000120106105n2001107000120101104P0P<P8P=P0P<P8PJP4P0P;P;PJP4P<P;P;f=RG/34P6P3E0n2001101000120106105n2001107000120101104P0P;P;P=P4P0P?P8P@PAP9PB%1G,6LPID4P0P>P>P@P4P?P>P>fARI#1RF=924P6P3E0n2001101000120106105n2001107000120101104=2@Dn2001101000120106105n2001107000120101104]0P6P0P;P;P0P;P;P=P4PAP9PG16KPPLD4=2@Dn2001101000120106105P0P<P8P=P0P;P;PJP3P<P;P;f?RJ/34P6P5E0n2001101000120106105P0P;P;P=P4P0P?P8P@PAP9f@RL16OFPGD4P0P>P>P@P4P?P>P>fE#1=924P6P3E0n2001101000120106105R2n2001107000120101104=2@Dn2001101000120106105n2001107000120101104]0^:8P6PAP9PO%1J,6BPKD4P?P>P>A5A93RKPCP6E052@P@P?P>P>A5A95RCPKP4E0P0P?P8P@P6P2n2001107000120101104P?P>P>13I195A9PCP3E052@X4@P?P>P>13L595A9PKP4E0,;@PAP9PJ%1L,6GPBD4P6EFW0X78X8;X9;P4P6O2n2001101010121100100X4<P4P6O2n2001101010121101103P4O1b4b0P?P>P>PH137195A9P3E0,;@n0110201020100b6P0P<P8P=1315?746P0P;P;P=P4PAP913NMP7P1D4=2@Dn2001101000120106105n2001107000120101104eX38X18X0EX2;X5:P6DEW2o"). Qed.

(* [comment removed for export] *)
Definition qrec_mergeb (nb bytes : Z) : bool :=
  (Q_BATCH_BYTES * nb <? bytes) && (bytes * 100 <? Q_BATCH_BYTES * nb * 200).

(* [comment removed for export] *)
Definition qrec_fun (X : list bq) (bytes min_size : Z) : list bq * list bq * Z :=
  let '(gl, ex) := (if qrec_mergeb (Z.of_nat (length X)) bytes then amerge_fun X else (X, [])) in
  let '(taken, rest, bytes2) := deq_bq gl (bytes - Q_BATCH_BYTES * Z.of_nat (length ex)) min_size in
  (rest, ex ++ taken, bytes2).

End CANSEC1.
Notation QREC_FRAME := 80 (only parsing).
Notation QREC_FRONT_STACK := 96 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition qrec_front_post (L : alayout) (X : list bq) (bytes min_size lo : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 a0 a4 a5 a6 a7 t3 t4 t5 t6 tbw : word) m',
    let '(rest, T, bytes2) := qrec_fun X bytes min_size in
    ms' = MS (mkR (Z_to_bv 64 0x335d0) (Z_to_bv 64 (bv_unsigned sp - QREC_FRAME)) gp tp t0 t1 t2 xs0 xs1
                  a0 (Z_to_bv 64 (bv_unsigned sp - QREC_FRAME)) a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x337c8) fc None m' (seg_rom bsegs)
    /\ munch ([(bv_unsigned sp - QREC_FRONT_STACK, bv_unsigned sp); (AQ_MUTEX, AQ_MUTEX + 4); (AQ_GCACHE, AQ_GCACHE + 32)]
              ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) X)%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp - QREC_FRAME)
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' (bv_unsigned sp - QREC_FRAME)
         [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T 0)); C8 (Z_to_bv 64 (tlast L T 0)); C8 tbw]
    /\ rw_cells bsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length rest))); C8 (Z_to_bv 64 (tfirst L rest 0)); C8 (Z_to_bv 64 (tlast L rest 0));
                                    C8 (Z_to_bv 64 bytes2)]
    /\ chain L m' rest 0 /\ chain L m' T 0
    /\ bytes2 = batches_bytes (map fst rest) /\ bytes2 <= min_size.

Definition qrec_front_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (X : list bq) (bytes min_size lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - QREC_FRONT_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 min_size -> 0 <= min_size < 2^63 ->
  (* [comment removed for export] *)
  rw_cells bsegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 (Z.of_nat (length X))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L X 0)); C8 (Z_to_bv 64 bytes)] ->
  chain L m X 0 ->
  Forall (bgeom L AQ_GCACHE (bv_unsigned sp - QREC_FRAME)) X -> Forall (fun x => 0 <= qb_slot (snd x)) X ->
  NoDup (map (fun x => qb_slot (snd x)) X) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X -> bytes = batches_bytes (map fst X) -> bytes < 2^56 ->
  Z.of_nat (length X) < 2^40 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) X ->
  evtF bsegs RNG (qrec_front_post L X bytes min_size lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33460) fc None m (seg_rom bsegs)).
End CANSEC2.
