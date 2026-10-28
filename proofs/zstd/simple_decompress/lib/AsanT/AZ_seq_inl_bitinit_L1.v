From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable AsanEmbed.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_kx AZ_globals AZ_globalsR AZ_huf_iface AZ_seq_bit_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Definition SQ_INL_BITINIT_L1_ENTRY : Z := 0x89cb8.
Definition SQ_INL_BITINIT_L1_EXIT : Z := 0x8a130.
Definition SQ_INL_BITINIT_L1_ERR : Z := 0x8e5a0.

Definition sq_inl_bitinit_L1_post (ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a6 s4 s6 s8 s9 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (FRB BD SEQ n TP T : Z) (m : amem) : machine_state -> Prop :=
  fun ms' =>
    (exists a2' a4' a5' a7' s11' m' cw bc jpad,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FRB) (Z_to_bv 64 (T + 4)) (Z_to_bv 64 (SEQ + 8)) a2' (Z_to_bv 64 T) a4' a5' a6 a7'
                    (Z_to_bv 64 ASHOFF) (Z_to_bv 64 SEQ) s4 (Z_to_bv 64 BD) s6 (Z_to_bv 64 TP) s8 s9 s10 s11' t3 t4 t5 t6)
               F (Z_to_bv 64 SQ_INL_BITINIT_L1_EXIT) fc None m' (seg_rom bsegs)
      /\ munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' BD (sbd_cells cw bc jpad (bitd_ptr SEQ n) SEQ)
      /\ rw_cells bsegs m' (FRB + 32) [C8 a0] /\ rw_cells bsegs m' (FRB + 56) [C8 a4]
      /\ rw_cells bsegs m' (FRB + 64) [C8 a3] /\ rw_cells bsegs m' (FRB + 104) [C8 a2]
      /\ 1 <= n /\ 1 <= bc <= 64 /\ (8 <= n -> bc <= 8) /\ bit_okS SEQ n bc (bitd_ptr SEQ n))
    \/
    (exists a0' a1' a2' a3' a4' a5' a7' s11' m' bs c32 c56 c64 c104,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FRB) a0' a1' a2' a3' a4' a5' a6 a7'
                    (Z_to_bv 64 ASHOFF) (Z_to_bv 64 SEQ) s4 (Z_to_bv 64 BD) s6 (Z_to_bv 64 TP) s8 s9 s10 s11' t3 t4 t5 t6)
               F (Z_to_bv 64 SQ_INL_BITINIT_L1_ERR) fc None m' (seg_rom bsegs)
      /\ munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' BD [CB 40 bs]
      /\ rw_cells bsegs m' (FRB + 32) [C8 c32] /\ rw_cells bsegs m' (FRB + 56) [C8 c56]
      /\ rw_cells bsegs m' (FRB + 64) [C8 c64] /\ rw_cells bsegs m' (FRB + 104) [C8 c104]).

Definition sq_inl_bitinit_L1_stmt_if (CND : Z -> Prop) : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 s10 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (FRB BD SEQ TP T : Z) (c32 c56 c64 c104 : word) (junk sqb : list byte),
  rw_cells bsegs m BD [CB 40 junk] ->
  rw_cells bsegs m (FRB + 32) [C8 c32] -> rw_cells bsegs m (FRB + 56) [C8 c56] ->
  rw_cells bsegs m (FRB + 64) [C8 c64] -> rw_cells bsegs m (FRB + 104) [C8 c104] ->
  rw_cells bsegs m TP [C8 (Z_to_bv 64 T)] -> bytes_at bsegs m SEQ sqb ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SEQ -> SEQ + Z.of_nat (length sqb) < 2^47 ->
  4096 <= FRB -> FRB + 112 < 2^47 -> 4096 <= TP -> TP + 8 < 2^47 -> 4096 <= T -> T + 8 < 2^47 ->
  BD mod 8 = 0 -> FRB mod 8 = 0 -> TP mod 8 = 0 -> T mod 4 = 0 ->
  (BD + 40 <= FRB + 32 \/ FRB + 112 <= BD) ->
  (1 <= Z.of_nat (length sqb) -> BD + 40 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= BD) ->
  (1 <= Z.of_nat (length sqb) -> FRB + 112 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= FRB + 32) ->
  (BD + 40 <= TP \/ TP + 8 <= BD) -> (FRB + 112 <= TP \/ TP + 8 <= FRB + 32) ->
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> app_blk (FRB + 32) (FRB + 112) -> rng RNG (FRB + 32) 80 ->
  aro RNG m TP 8 -> aro RNG m T 8 -> (1 <= Z.of_nat (length sqb) -> aro RNG m SEQ (Z.of_nat (length sqb))) ->
  rng_aimg RNG -> art m -> mem_inv bsegs m ->
  CND (Z.of_nat (length sqb)) ->
  evtF bsegs RNG (sq_inl_bitinit_L1_post ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a6 s4 s6 s8 s9 s10 t3 t4 t5 t6 F fc
                    FRB BD SEQ (Z.of_nat (length sqb)) TP T m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FRB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ASHOFF) (Z_to_bv 64 SEQ) s4 (Z_to_bv 64 BD) s6 (Z_to_bv 64 TP) s8 s9 s10
               (Z_to_bv 64 (Z.of_nat (length sqb))) t3 t4 t5 t6)
          F (Z_to_bv 64 SQ_INL_BITINIT_L1_ENTRY) fc None m (seg_rom bsegs)).

Definition sq_inl_bitinit_L1_stmt : Prop := sq_inl_bitinit_L1_stmt_if (fun _ => True).

Ltac kxa_norm ::= unfold shspan in *.
Ltac kx_pull ::= kx_pull1; kx_pull1.
Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

Tactic Notation "kx_autoFLAx_v" constr(VMAX) uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  let CH := kxl_all_chunks in
  kx_autoFLA_core (VMAX : Z) stops (FUEL : nat) true CH aks kzs rrs wws.

Ltac bi_enum B K :=
  let BCE := fresh "BCE" in
  match goal with
  | BDC : rw_cells _ _ B _ |- _ =>
    lazymatch type of BDC with
    | context [C4 (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + ?c))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (-1 * Z.lxor v 31 + c) mod 2^64) && ((-1 * Z.lxor v 31 + c) mod 2^64 <=? K))%bool end
    | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + ?c))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + c) mod 2^64) && ((v + c) mod 2^64 <=? K))%bool end
    | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e)))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? K))%bool end
    | context [C4 (edenot ?E ?e)] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? K))%bool end
    end;
    cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2
  end.

Ltac bi_bases mc acc :=
  match goal with
  | H : rw_cells _ mc ?B _ |- _ => lazymatch acc with context [H] => fail | _ => bi_bases mc (H, B, acc) end
  | _ => acc
  end.

Ltac bi_slot :=
  first [ match goal with H : rw_cells _ _ ?S [C8 _] |- rw_cells _ _ ?S2 _ => constr_eq S S2; exact H end
        | lazymatch goal with |- rw_cells _ ?mc ?S2 _ => let L := bi_bases mc tt in fail 99 "SLOT" S2 L end ].

Ltac bi_regs :=
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ =>
      first [ reflexivity | (f_equal; try reflexivity; f_equal; try reflexivity; f_equal; lia)
            | (f_equal; try reflexivity; f_equal; try reflexivity; match goal with |- ?G => fail 99 "REGS" G end) ]
  end.

Ltac bi_close_ok B N S :=
  apply evtF_done;
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
    unfold sq_inl_bitinit_L1_post; left;
    first [ match goal with BDC' : rw_cells _ mc B _ |- _ => idtac end
          | let L := bi_bases mc tt in fail 99 "OK noBD" L ];
    match goal with BDC' : rw_cells _ mc B ?cs |- _ =>
      do 5 eexists; exists mc;
      first [ lazymatch cs with
              | context [C4 (Z_to_bv 64 ?v)] => eexists; exists (v mod 2^64); eexists
              | context [C4 (edenot ?E ?e)] => eexists; exists (bv_unsigned (edenot E e) mod 2^64); eexists
              end
            | fail 99 "OK noC4" cs ];
      split; [bi_regs|];
      first [ split; [eassumption|]; split; [eassumption|]; split; [eassumption|]
            | lazymatch goal with |- ?G1 /\ ?G2 /\ ?G3 /\ _ => fail 99 "OK mem" G1 G2 G3 end ];
      split; [unfold sbd_cells, bitd_ptr; first [rewrite KXS.Z_to_bv64_mod, ?Z_to_bv_bv_unsigned | fail 99 "OK rw"];
              first [ replace (8 <=? N) with true by (symmetry; apply Z.leb_le; lia);
                      replace (S + N - 8) with (S + N + -8) by lia; exact BDC'
                    | replace (8 <=? N) with false by (symmetry; apply Z.leb_gt; lia); exact BDC'
                    | exact BDC'
                    | lazymatch goal with |- rw_cells _ _ _ [_; _; _; ?P1; ?S1; ?L1] =>
                        lazymatch cs with
                        | [_; _; _; ?P2; ?S2; ?L2] => fail 99 "OK BDptr" P1 P2 S1 S2 L1 L2
                        | _ => let k := eval cbv beta iota delta [length] in (length cs) in fail 99 "OK BDlen" k
                        end
                      end ]|]
    end
  end;
  do 4 (split; [bi_slot|]);
  first [ split; [lia|]; split; [lia|]; split; [intros; lia|];
          unfold bit_okS, bitd_ptr; destruct (Z.leb_spec 8 N); intros; lia
        | match goal with |- ?G => fail 99 "OK tail" G end ].

Ltac bi_close_err B :=
  apply evtF_done;
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
    unfold sq_inl_bitinit_L1_post; right;
    first [ match goal with H : rw_cells _ mc B _ |- _ => idtac end
          | let L := bi_bases mc tt in fail 99 "ERR noBD" L ];
    lazymatch goal with H : rw_cells _ mc B _ |- _ =>
      let bs := fresh "bs" in let Hbs := fresh "Hbs" in
      destruct (rw_cells_forget bsegs _ _ _ H) as [bs Hbs];
      do 8 eexists; exists mc, bs; do 4 eexists;
      split; [bi_regs|];
      first [ split; [eassumption|]; split; [eassumption|]; split; [eassumption|]
            | lazymatch goal with |- ?G1 /\ ?G2 /\ ?G3 /\ _ => fail 99 "ERR mem" G1 G2 G3 end ];
      split; [exact Hbs|]
    end
  end;
  do 3 (split; [bi_slot|]); bi_slot.

Lemma sq_inl_bitinit_L1_c0 : sq_inl_bitinit_L1_stmt_if (fun n => n = 0).
Proof.
  unfold sq_inl_bitinit_L1_stmt_if, SQ_INL_BITINIT_L1_ENTRY. intros until sqb.
  intros HBD H32 H56 H64 H104 HTP SQB R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 A1 A2 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5
         APB AROB APF RGF AROTP AROT AROS RIMG ART MI C.
  cbv beta in C.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct AROT as (UT & RGT & RGTS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (FRBB : FRB + 112 <= KLOW \/ KHIGH <= FRB + 32) by (unfold app_blk in APF; clear - APF; lia).
  unfold KLOW, KHIGH in BDB, FRBB.
  assert (MU : munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m)
    by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLAx [KAUnp BD 40; KAUnp TP 8; KAUnp T 8; KAApp BD 40; KAApp (FRB + 32) 80]
      [SQ_INL_BITINIT_L1_EXIT; SQ_INL_BITINIT_L1_ERR] 400%nat
      [KZRange n 0 0;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 112); KZRange TP 4096 (2^47 - 8); KZRange T 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign T 4;
       KZWr BD 40; KZWr (FRB + 32) 8; KZWr (FRB + 56) 8; KZWr (FRB + 64) 8; KZWr (FRB + 104) 8;
       KZDisj (FRB + 32) 8 BD 40; KZDisj (FRB + 56) 8 BD 40; KZDisj (FRB + 64) 8 BD 40; KZDisj (FRB + 104) 8 BD 40;
       KZDisj (FRB + 32) 8 (FRB + 56) 8; KZDisj (FRB + 32) 8 (FRB + 64) 8; KZDisj (FRB + 32) 8 (FRB + 104) 8;
       KZDisj (FRB + 56) 8 (FRB + 64) 8; KZDisj (FRB + 56) 8 (FRB + 104) 8; KZDisj (FRB + 64) 8 (FRB + 104) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 32) 8 TP 8; KZDisj (FRB + 56) 8 TP 8; KZDisj (FRB + 64) 8 TP 8; KZDisj (FRB + 104) 8 TP 8]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8); (TP, 8)]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RGF | kx_acc RGTP | kx_acc RGT | kx_acc RGBS | kx_acc RGTPS | kx_acc RGTS | kx_acc RIMG] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = SQ_INL_BITINIT_L1_EXIT) by (unfold SQ_INL_BITINIT_L1_EXIT; reflexivity)
              | assert (UPC = SQ_INL_BITINIT_L1_ERR) by (unfold SQ_INL_BITINIT_L1_ERR; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP _ _ _ => fail 99 "accP left"
    | |- sc_resid _ _ _ ?S => kx_side_pre; match goal with |- ?G => fail 99 "sc_resid left" G end
    | |- _ /\ _ /\ (?A + _ <= ?B \/ _) => fail 99 "disj left" A B
    | |- ?A /\ ?B => fail 99 "conj left" A
    | |- ?A <= ?B => fail 99 "le left"
    | |- rdn _ _ _ _ = _ => fail 99 "rdn left"
    | |- _ = _ => fail 99 "eq left"
    | |- _ => fail 99 "other goal"
  end.
  all: clear GOT RIC SHB INI LAY REAL.
  all: kx_mem.
  all: try (bi_enum BD 64).
  all: kx_abs.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        let b := eval vm_compute in (Z.eqb UPC SQ_INL_BITINIT_L1_EXIT) in
        lazymatch b with true => bi_close_ok BD n SEQ | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_L1_c1 : sq_inl_bitinit_L1_stmt_if (fun n => n = 1).
Proof.
  unfold sq_inl_bitinit_L1_stmt_if, SQ_INL_BITINIT_L1_ENTRY. intros until sqb.
  intros HBD H32 H56 H64 H104 HTP SQB R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 A1 A2 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5
         APB AROB APF RGF AROTP AROT AROS RIMG ART MI C.
  cbv beta in C.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct AROT as (UT & RGT & RGTS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (FRBB : FRB + 112 <= KLOW \/ KHIGH <= FRB + 32) by (unfold app_blk in APF; clear - APF; lia).
  unfold KLOW, KHIGH in BDB, FRBB.
  assert (MU : munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m)
    by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  destruct (AROS ltac:(lia)) as (US & RGS & RGSS). pose proof (DJ2 ltac:(lia)) as DJ2a. pose proof (DJ3 ltac:(lia)) as DJ3a.
  clear AROS DJ2 DJ3.
  kx_autoFLAx [KAUnp BD 40; KAUnp SEQ n; KAUnp TP 8; KAUnp T 8; KAApp BD 40; KAApp (FRB + 32) 80]
      [SQ_INL_BITINIT_L1_EXIT; SQ_INL_BITINIT_L1_ERR] 400%nat
      [KZRange n 1 1;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 112); KZRange TP 4096 (2^47 - 8); KZRange T 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign T 4;
       KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 32) 8; KZWr (FRB + 56) 8; KZWr (FRB + 64) 8; KZWr (FRB + 104) 8;
       KZDisj (FRB + 32) 8 BD 40; KZDisj (FRB + 56) 8 BD 40; KZDisj (FRB + 64) 8 BD 40; KZDisj (FRB + 104) 8 BD 40;
       KZDisj (FRB + 32) 8 (FRB + 56) 8; KZDisj (FRB + 32) 8 (FRB + 64) 8; KZDisj (FRB + 32) 8 (FRB + 104) 8;
       KZDisj (FRB + 56) 8 (FRB + 64) 8; KZDisj (FRB + 56) 8 (FRB + 104) 8; KZDisj (FRB + 64) 8 (FRB + 104) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 32) 8 TP 8; KZDisj (FRB + 56) 8 TP 8; KZDisj (FRB + 64) 8 TP 8; KZDisj (FRB + 104) 8 TP 8;
       KZDisj BD 40 SEQ n; KZDisj (FRB + 32) 8 SEQ n; KZDisj (FRB + 56) 8 SEQ n; KZDisj (FRB + 64) 8 SEQ n; KZDisj (FRB + 104) 8 SEQ n]
      [(SEQ, n); (BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8); (TP, 8)]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RGF | kx_acc RGTP | kx_acc RGT | kx_acc RGBS | kx_acc RGTPS | kx_acc RGTS | kx_acc RIMG | kx_acc RGS | kx_acc RGSS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = SQ_INL_BITINIT_L1_EXIT) by (unfold SQ_INL_BITINIT_L1_EXIT; reflexivity)
              | assert (UPC = SQ_INL_BITINIT_L1_ERR) by (unfold SQ_INL_BITINIT_L1_ERR; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP _ _ _ => fail 99 "accP left"
    | |- sc_resid _ _ _ ?S => kx_side_pre; match goal with |- ?G => fail 99 "sc_resid left" G end
    | |- _ /\ _ /\ (?A + _ <= ?B \/ _) => fail 99 "disj left" A B
    | |- ?A /\ ?B => fail 99 "conj left" A
    | |- ?A <= ?B => fail 99 "le left"
    | |- rdn _ _ _ _ = _ => fail 99 "rdn left"
    | |- _ = _ => fail 99 "eq left"
    | |- _ => fail 99 "other goal"
  end.
  all: clear GOT RIC SHB INI LAY REAL.
  all: kx_mem.
  all: try (bi_enum BD 64).
  all: kx_abs.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        let b := eval vm_compute in (Z.eqb UPC SQ_INL_BITINIT_L1_EXIT) in
        lazymatch b with true => bi_close_ok BD n SEQ | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_L1_c2 : sq_inl_bitinit_L1_stmt_if (fun n => n = 2).
Proof.
  unfold sq_inl_bitinit_L1_stmt_if, SQ_INL_BITINIT_L1_ENTRY. intros until sqb.
  intros HBD H32 H56 H64 H104 HTP SQB R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 A1 A2 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5
         APB AROB APF RGF AROTP AROT AROS RIMG ART MI C.
  cbv beta in C.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct AROT as (UT & RGT & RGTS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (FRBB : FRB + 112 <= KLOW \/ KHIGH <= FRB + 32) by (unfold app_blk in APF; clear - APF; lia).
  unfold KLOW, KHIGH in BDB, FRBB.
  assert (MU : munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m)
    by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  destruct (AROS ltac:(lia)) as (US & RGS & RGSS). pose proof (DJ2 ltac:(lia)) as DJ2a. pose proof (DJ3 ltac:(lia)) as DJ3a.
  clear AROS DJ2 DJ3.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SEQ n; KAUnp TP 8; KAUnp T 8; KAApp BD 40; KAApp (FRB + 32) 80]
      [SQ_INL_BITINIT_L1_EXIT; SQ_INL_BITINIT_L1_ERR] 400%nat
      [KZRange n 2 2; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 112); KZRange TP 4096 (2^47 - 8); KZRange T 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign T 4;
       KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 32) 8; KZWr (FRB + 56) 8; KZWr (FRB + 64) 8; KZWr (FRB + 104) 8;
       KZDisj (FRB + 32) 8 BD 40; KZDisj (FRB + 56) 8 BD 40; KZDisj (FRB + 64) 8 BD 40; KZDisj (FRB + 104) 8 BD 40;
       KZDisj (FRB + 32) 8 (FRB + 56) 8; KZDisj (FRB + 32) 8 (FRB + 64) 8; KZDisj (FRB + 32) 8 (FRB + 104) 8;
       KZDisj (FRB + 56) 8 (FRB + 64) 8; KZDisj (FRB + 56) 8 (FRB + 104) 8; KZDisj (FRB + 64) 8 (FRB + 104) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 32) 8 TP 8; KZDisj (FRB + 56) 8 TP 8; KZDisj (FRB + 64) 8 TP 8; KZDisj (FRB + 104) 8 TP 8;
       KZDisj BD 40 SEQ n; KZDisj (FRB + 32) 8 SEQ n; KZDisj (FRB + 56) 8 SEQ n; KZDisj (FRB + 64) 8 SEQ n; KZDisj (FRB + 104) 8 SEQ n]
      [(SEQ, n); (BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8); (TP, 8)]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RGF | kx_acc RGTP | kx_acc RGT | kx_acc RGBS | kx_acc RGTPS | kx_acc RGTS | kx_acc RIMG | kx_acc RGS | kx_acc RGSS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = SQ_INL_BITINIT_L1_EXIT) by (unfold SQ_INL_BITINIT_L1_EXIT; reflexivity)
              | assert (UPC = SQ_INL_BITINIT_L1_ERR) by (unfold SQ_INL_BITINIT_L1_ERR; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP _ _ _ => fail 99 "accP left"
    | |- sc_resid _ _ _ ?S => kx_side_pre; match goal with |- ?G => fail 99 "sc_resid left" G end
    | |- _ /\ _ /\ (?A + _ <= ?B \/ _) => fail 99 "disj left" A B
    | |- ?A /\ ?B => fail 99 "conj left" A
    | |- ?A <= ?B => fail 99 "le left"
    | |- rdn _ _ _ _ = _ => fail 99 "rdn left"
    | |- _ = _ => fail 99 "eq left"
    | |- _ => fail 99 "other goal"
  end.
  all: clear GOT RIC SHB INI LAY REAL.
  all: kx_mem.
  all: try (bi_enum BD 64).
  all: kx_abs.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        let b := eval vm_compute in (Z.eqb UPC SQ_INL_BITINIT_L1_EXIT) in
        lazymatch b with true => bi_close_ok BD n SEQ | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_L1_c3 : sq_inl_bitinit_L1_stmt_if (fun n => n = 3).
Proof.
  unfold sq_inl_bitinit_L1_stmt_if, SQ_INL_BITINIT_L1_ENTRY. intros until sqb.
  intros HBD H32 H56 H64 H104 HTP SQB R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 A1 A2 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5
         APB AROB APF RGF AROTP AROT AROS RIMG ART MI C.
  cbv beta in C.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct AROT as (UT & RGT & RGTS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (FRBB : FRB + 112 <= KLOW \/ KHIGH <= FRB + 32) by (unfold app_blk in APF; clear - APF; lia).
  unfold KLOW, KHIGH in BDB, FRBB.
  assert (MU : munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m)
    by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  destruct (AROS ltac:(lia)) as (US & RGS & RGSS). pose proof (DJ2 ltac:(lia)) as DJ2a. pose proof (DJ3 ltac:(lia)) as DJ3a.
  clear AROS DJ2 DJ3.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SEQ n; KAUnp TP 8; KAUnp T 8; KAApp BD 40; KAApp (FRB + 32) 80]
      [SQ_INL_BITINIT_L1_EXIT; SQ_INL_BITINIT_L1_ERR] 400%nat
      [KZRange n 3 3; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 112); KZRange TP 4096 (2^47 - 8); KZRange T 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign T 4;
       KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 32) 8; KZWr (FRB + 56) 8; KZWr (FRB + 64) 8; KZWr (FRB + 104) 8;
       KZDisj (FRB + 32) 8 BD 40; KZDisj (FRB + 56) 8 BD 40; KZDisj (FRB + 64) 8 BD 40; KZDisj (FRB + 104) 8 BD 40;
       KZDisj (FRB + 32) 8 (FRB + 56) 8; KZDisj (FRB + 32) 8 (FRB + 64) 8; KZDisj (FRB + 32) 8 (FRB + 104) 8;
       KZDisj (FRB + 56) 8 (FRB + 64) 8; KZDisj (FRB + 56) 8 (FRB + 104) 8; KZDisj (FRB + 64) 8 (FRB + 104) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 32) 8 TP 8; KZDisj (FRB + 56) 8 TP 8; KZDisj (FRB + 64) 8 TP 8; KZDisj (FRB + 104) 8 TP 8;
       KZDisj BD 40 SEQ n; KZDisj (FRB + 32) 8 SEQ n; KZDisj (FRB + 56) 8 SEQ n; KZDisj (FRB + 64) 8 SEQ n; KZDisj (FRB + 104) 8 SEQ n]
      [(SEQ, n); (BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8); (TP, 8)]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RGF | kx_acc RGTP | kx_acc RGT | kx_acc RGBS | kx_acc RGTPS | kx_acc RGTS | kx_acc RIMG | kx_acc RGS | kx_acc RGSS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = SQ_INL_BITINIT_L1_EXIT) by (unfold SQ_INL_BITINIT_L1_EXIT; reflexivity)
              | assert (UPC = SQ_INL_BITINIT_L1_ERR) by (unfold SQ_INL_BITINIT_L1_ERR; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP _ _ _ => fail 99 "accP left"
    | |- sc_resid _ _ _ ?S => kx_side_pre; match goal with |- ?G => fail 99 "sc_resid left" G end
    | |- _ /\ _ /\ (?A + _ <= ?B \/ _) => fail 99 "disj left" A B
    | |- ?A /\ ?B => fail 99 "conj left" A
    | |- ?A <= ?B => fail 99 "le left"
    | |- rdn _ _ _ _ = _ => fail 99 "rdn left"
    | |- _ = _ => fail 99 "eq left"
    | |- _ => fail 99 "other goal"
  end.
  all: clear GOT RIC SHB INI LAY REAL.
  all: kx_mem.
  all: try (bi_enum BD 64).
  all: kx_abs.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        let b := eval vm_compute in (Z.eqb UPC SQ_INL_BITINIT_L1_EXIT) in
        lazymatch b with true => bi_close_ok BD n SEQ | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_L1_c4 : sq_inl_bitinit_L1_stmt_if (fun n => n = 4).
Proof.
  unfold sq_inl_bitinit_L1_stmt_if, SQ_INL_BITINIT_L1_ENTRY. intros until sqb.
  intros HBD H32 H56 H64 H104 HTP SQB R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 A1 A2 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5
         APB AROB APF RGF AROTP AROT AROS RIMG ART MI C.
  cbv beta in C.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct AROT as (UT & RGT & RGTS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (FRBB : FRB + 112 <= KLOW \/ KHIGH <= FRB + 32) by (unfold app_blk in APF; clear - APF; lia).
  unfold KLOW, KHIGH in BDB, FRBB.
  assert (MU : munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m)
    by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  destruct (AROS ltac:(lia)) as (US & RGS & RGSS). pose proof (DJ2 ltac:(lia)) as DJ2a. pose proof (DJ3 ltac:(lia)) as DJ3a.
  clear AROS DJ2 DJ3.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SEQ n; KAUnp TP 8; KAUnp T 8; KAApp BD 40; KAApp (FRB + 32) 80]
      [SQ_INL_BITINIT_L1_EXIT; SQ_INL_BITINIT_L1_ERR] 400%nat
      [KZRange n 4 4; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 112); KZRange TP 4096 (2^47 - 8); KZRange T 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign T 4;
       KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 32) 8; KZWr (FRB + 56) 8; KZWr (FRB + 64) 8; KZWr (FRB + 104) 8;
       KZDisj (FRB + 32) 8 BD 40; KZDisj (FRB + 56) 8 BD 40; KZDisj (FRB + 64) 8 BD 40; KZDisj (FRB + 104) 8 BD 40;
       KZDisj (FRB + 32) 8 (FRB + 56) 8; KZDisj (FRB + 32) 8 (FRB + 64) 8; KZDisj (FRB + 32) 8 (FRB + 104) 8;
       KZDisj (FRB + 56) 8 (FRB + 64) 8; KZDisj (FRB + 56) 8 (FRB + 104) 8; KZDisj (FRB + 64) 8 (FRB + 104) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 32) 8 TP 8; KZDisj (FRB + 56) 8 TP 8; KZDisj (FRB + 64) 8 TP 8; KZDisj (FRB + 104) 8 TP 8;
       KZDisj BD 40 SEQ n; KZDisj (FRB + 32) 8 SEQ n; KZDisj (FRB + 56) 8 SEQ n; KZDisj (FRB + 64) 8 SEQ n; KZDisj (FRB + 104) 8 SEQ n]
      [(SEQ, n); (BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8); (TP, 8)]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RGF | kx_acc RGTP | kx_acc RGT | kx_acc RGBS | kx_acc RGTPS | kx_acc RGTS | kx_acc RIMG | kx_acc RGS | kx_acc RGSS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = SQ_INL_BITINIT_L1_EXIT) by (unfold SQ_INL_BITINIT_L1_EXIT; reflexivity)
              | assert (UPC = SQ_INL_BITINIT_L1_ERR) by (unfold SQ_INL_BITINIT_L1_ERR; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP _ _ _ => fail 99 "accP left"
    | |- sc_resid _ _ _ ?S => kx_side_pre; match goal with |- ?G => fail 99 "sc_resid left" G end
    | |- _ /\ _ /\ (?A + _ <= ?B \/ _) => fail 99 "disj left" A B
    | |- ?A /\ ?B => fail 99 "conj left" A
    | |- ?A <= ?B => fail 99 "le left"
    | |- rdn _ _ _ _ = _ => fail 99 "rdn left"
    | |- _ = _ => fail 99 "eq left"
    | |- _ => fail 99 "other goal"
  end.
  all: clear GOT RIC SHB INI LAY REAL.
  all: kx_mem.
  all: try (bi_enum BD 64).
  all: kx_abs.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        let b := eval vm_compute in (Z.eqb UPC SQ_INL_BITINIT_L1_EXIT) in
        lazymatch b with true => bi_close_ok BD n SEQ | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_L1_c5 : sq_inl_bitinit_L1_stmt_if (fun n => n = 5).
Proof.
  unfold sq_inl_bitinit_L1_stmt_if, SQ_INL_BITINIT_L1_ENTRY. intros until sqb.
  intros HBD H32 H56 H64 H104 HTP SQB R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 A1 A2 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5
         APB AROB APF RGF AROTP AROT AROS RIMG ART MI C.
  cbv beta in C.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct AROT as (UT & RGT & RGTS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (FRBB : FRB + 112 <= KLOW \/ KHIGH <= FRB + 32) by (unfold app_blk in APF; clear - APF; lia).
  unfold KLOW, KHIGH in BDB, FRBB.
  assert (MU : munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m)
    by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  destruct (AROS ltac:(lia)) as (US & RGS & RGSS). pose proof (DJ2 ltac:(lia)) as DJ2a. pose proof (DJ3 ltac:(lia)) as DJ3a.
  clear AROS DJ2 DJ3.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SEQ n; KAUnp TP 8; KAUnp T 8; KAApp BD 40; KAApp (FRB + 32) 80]
      [SQ_INL_BITINIT_L1_EXIT; SQ_INL_BITINIT_L1_ERR] 400%nat
      [KZRange n 5 5; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 112); KZRange TP 4096 (2^47 - 8); KZRange T 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign T 4;
       KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 32) 8; KZWr (FRB + 56) 8; KZWr (FRB + 64) 8; KZWr (FRB + 104) 8;
       KZDisj (FRB + 32) 8 BD 40; KZDisj (FRB + 56) 8 BD 40; KZDisj (FRB + 64) 8 BD 40; KZDisj (FRB + 104) 8 BD 40;
       KZDisj (FRB + 32) 8 (FRB + 56) 8; KZDisj (FRB + 32) 8 (FRB + 64) 8; KZDisj (FRB + 32) 8 (FRB + 104) 8;
       KZDisj (FRB + 56) 8 (FRB + 64) 8; KZDisj (FRB + 56) 8 (FRB + 104) 8; KZDisj (FRB + 64) 8 (FRB + 104) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 32) 8 TP 8; KZDisj (FRB + 56) 8 TP 8; KZDisj (FRB + 64) 8 TP 8; KZDisj (FRB + 104) 8 TP 8;
       KZDisj BD 40 SEQ n; KZDisj (FRB + 32) 8 SEQ n; KZDisj (FRB + 56) 8 SEQ n; KZDisj (FRB + 64) 8 SEQ n; KZDisj (FRB + 104) 8 SEQ n]
      [(SEQ, n); (BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8); (TP, 8)]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RGF | kx_acc RGTP | kx_acc RGT | kx_acc RGBS | kx_acc RGTPS | kx_acc RGTS | kx_acc RIMG | kx_acc RGS | kx_acc RGSS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = SQ_INL_BITINIT_L1_EXIT) by (unfold SQ_INL_BITINIT_L1_EXIT; reflexivity)
              | assert (UPC = SQ_INL_BITINIT_L1_ERR) by (unfold SQ_INL_BITINIT_L1_ERR; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP _ _ _ => fail 99 "accP left"
    | |- sc_resid _ _ _ ?S => kx_side_pre; match goal with |- ?G => fail 99 "sc_resid left" G end
    | |- _ /\ _ /\ (?A + _ <= ?B \/ _) => fail 99 "disj left" A B
    | |- ?A /\ ?B => fail 99 "conj left" A
    | |- ?A <= ?B => fail 99 "le left"
    | |- rdn _ _ _ _ = _ => fail 99 "rdn left"
    | |- _ = _ => fail 99 "eq left"
    | |- _ => fail 99 "other goal"
  end.
  all: clear GOT RIC SHB INI LAY REAL.
  all: kx_mem.
  all: try (bi_enum BD 64).
  all: kx_abs.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        let b := eval vm_compute in (Z.eqb UPC SQ_INL_BITINIT_L1_EXIT) in
        lazymatch b with true => bi_close_ok BD n SEQ | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_L1_c6 : sq_inl_bitinit_L1_stmt_if (fun n => n = 6).
Proof.
  unfold sq_inl_bitinit_L1_stmt_if, SQ_INL_BITINIT_L1_ENTRY. intros until sqb.
  intros HBD H32 H56 H64 H104 HTP SQB R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 A1 A2 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5
         APB AROB APF RGF AROTP AROT AROS RIMG ART MI C.
  cbv beta in C.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct AROT as (UT & RGT & RGTS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (FRBB : FRB + 112 <= KLOW \/ KHIGH <= FRB + 32) by (unfold app_blk in APF; clear - APF; lia).
  unfold KLOW, KHIGH in BDB, FRBB.
  assert (MU : munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m)
    by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  destruct (AROS ltac:(lia)) as (US & RGS & RGSS). pose proof (DJ2 ltac:(lia)) as DJ2a. pose proof (DJ3 ltac:(lia)) as DJ3a.
  clear AROS DJ2 DJ3.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SEQ n; KAUnp TP 8; KAUnp T 8; KAApp BD 40; KAApp (FRB + 32) 80]
      [SQ_INL_BITINIT_L1_EXIT; SQ_INL_BITINIT_L1_ERR] 400%nat
      [KZRange n 6 6; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 112); KZRange TP 4096 (2^47 - 8); KZRange T 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign T 4;
       KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 32) 8; KZWr (FRB + 56) 8; KZWr (FRB + 64) 8; KZWr (FRB + 104) 8;
       KZDisj (FRB + 32) 8 BD 40; KZDisj (FRB + 56) 8 BD 40; KZDisj (FRB + 64) 8 BD 40; KZDisj (FRB + 104) 8 BD 40;
       KZDisj (FRB + 32) 8 (FRB + 56) 8; KZDisj (FRB + 32) 8 (FRB + 64) 8; KZDisj (FRB + 32) 8 (FRB + 104) 8;
       KZDisj (FRB + 56) 8 (FRB + 64) 8; KZDisj (FRB + 56) 8 (FRB + 104) 8; KZDisj (FRB + 64) 8 (FRB + 104) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 32) 8 TP 8; KZDisj (FRB + 56) 8 TP 8; KZDisj (FRB + 64) 8 TP 8; KZDisj (FRB + 104) 8 TP 8;
       KZDisj BD 40 SEQ n; KZDisj (FRB + 32) 8 SEQ n; KZDisj (FRB + 56) 8 SEQ n; KZDisj (FRB + 64) 8 SEQ n; KZDisj (FRB + 104) 8 SEQ n]
      [(SEQ, n); (BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8); (TP, 8)]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RGF | kx_acc RGTP | kx_acc RGT | kx_acc RGBS | kx_acc RGTPS | kx_acc RGTS | kx_acc RIMG | kx_acc RGS | kx_acc RGSS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = SQ_INL_BITINIT_L1_EXIT) by (unfold SQ_INL_BITINIT_L1_EXIT; reflexivity)
              | assert (UPC = SQ_INL_BITINIT_L1_ERR) by (unfold SQ_INL_BITINIT_L1_ERR; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP _ _ _ => fail 99 "accP left"
    | |- sc_resid _ _ _ ?S => kx_side_pre; match goal with |- ?G => fail 99 "sc_resid left" G end
    | |- _ /\ _ /\ (?A + _ <= ?B \/ _) => fail 99 "disj left" A B
    | |- ?A /\ ?B => fail 99 "conj left" A
    | |- ?A <= ?B => fail 99 "le left"
    | |- rdn _ _ _ _ = _ => fail 99 "rdn left"
    | |- _ = _ => fail 99 "eq left"
    | |- _ => fail 99 "other goal"
  end.
  all: clear GOT RIC SHB INI LAY REAL.
  all: kx_mem.
  all: try (bi_enum BD 64).
  all: kx_abs.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        let b := eval vm_compute in (Z.eqb UPC SQ_INL_BITINIT_L1_EXIT) in
        lazymatch b with true => bi_close_ok BD n SEQ | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_L1_c7 : sq_inl_bitinit_L1_stmt_if (fun n => n = 7).
Proof.
  unfold sq_inl_bitinit_L1_stmt_if, SQ_INL_BITINIT_L1_ENTRY. intros until sqb.
  intros HBD H32 H56 H64 H104 HTP SQB R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 A1 A2 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5
         APB AROB APF RGF AROTP AROT AROS RIMG ART MI C.
  cbv beta in C.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct AROT as (UT & RGT & RGTS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (FRBB : FRB + 112 <= KLOW \/ KHIGH <= FRB + 32) by (unfold app_blk in APF; clear - APF; lia).
  unfold KLOW, KHIGH in BDB, FRBB.
  assert (MU : munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m)
    by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  destruct (AROS ltac:(lia)) as (US & RGS & RGSS). pose proof (DJ2 ltac:(lia)) as DJ2a. pose proof (DJ3 ltac:(lia)) as DJ3a.
  clear AROS DJ2 DJ3.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SEQ n; KAUnp TP 8; KAUnp T 8; KAApp BD 40; KAApp (FRB + 32) 80]
      [SQ_INL_BITINIT_L1_EXIT; SQ_INL_BITINIT_L1_ERR] 400%nat
      [KZRange n 7 7; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 112); KZRange TP 4096 (2^47 - 8); KZRange T 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign T 4;
       KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 32) 8; KZWr (FRB + 56) 8; KZWr (FRB + 64) 8; KZWr (FRB + 104) 8;
       KZDisj (FRB + 32) 8 BD 40; KZDisj (FRB + 56) 8 BD 40; KZDisj (FRB + 64) 8 BD 40; KZDisj (FRB + 104) 8 BD 40;
       KZDisj (FRB + 32) 8 (FRB + 56) 8; KZDisj (FRB + 32) 8 (FRB + 64) 8; KZDisj (FRB + 32) 8 (FRB + 104) 8;
       KZDisj (FRB + 56) 8 (FRB + 64) 8; KZDisj (FRB + 56) 8 (FRB + 104) 8; KZDisj (FRB + 64) 8 (FRB + 104) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 32) 8 TP 8; KZDisj (FRB + 56) 8 TP 8; KZDisj (FRB + 64) 8 TP 8; KZDisj (FRB + 104) 8 TP 8;
       KZDisj BD 40 SEQ n; KZDisj (FRB + 32) 8 SEQ n; KZDisj (FRB + 56) 8 SEQ n; KZDisj (FRB + 64) 8 SEQ n; KZDisj (FRB + 104) 8 SEQ n]
      [(SEQ, n); (BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8); (TP, 8)]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RGF | kx_acc RGTP | kx_acc RGT | kx_acc RGBS | kx_acc RGTPS | kx_acc RGTS | kx_acc RIMG | kx_acc RGS | kx_acc RGSS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = SQ_INL_BITINIT_L1_EXIT) by (unfold SQ_INL_BITINIT_L1_EXIT; reflexivity)
              | assert (UPC = SQ_INL_BITINIT_L1_ERR) by (unfold SQ_INL_BITINIT_L1_ERR; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP _ _ _ => fail 99 "accP left"
    | |- sc_resid _ _ _ ?S => kx_side_pre; match goal with |- ?G => fail 99 "sc_resid left" G end
    | |- _ /\ _ /\ (?A + _ <= ?B \/ _) => fail 99 "disj left" A B
    | |- ?A /\ ?B => fail 99 "conj left" A
    | |- ?A <= ?B => fail 99 "le left"
    | |- rdn _ _ _ _ = _ => fail 99 "rdn left"
    | |- _ = _ => fail 99 "eq left"
    | |- _ => fail 99 "other goal"
  end.
  all: clear GOT RIC SHB INI LAY REAL.
  all: kx_mem.
  all: try (bi_enum BD 64).
  all: kx_abs.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        let b := eval vm_compute in (Z.eqb UPC SQ_INL_BITINIT_L1_EXIT) in
        lazymatch b with true => bi_close_ok BD n SEQ | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_L1_c8 : sq_inl_bitinit_L1_stmt_if (fun n => 8 <= n).
Proof.
  unfold sq_inl_bitinit_L1_stmt_if, SQ_INL_BITINIT_L1_ENTRY. intros until sqb.
  intros HBD H32 H56 H64 H104 HTP SQB R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 A1 A2 A3 A4 DJ1 DJ2 DJ3 DJ4 DJ5
         APB AROB APF RGF AROTP AROT AROS RIMG ART MI C.
  cbv beta in C.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct AROT as (UT & RGT & RGTS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (FRBB : FRB + 112 <= KLOW \/ KHIGH <= FRB + 32) by (unfold app_blk in APF; clear - APF; lia).
  unfold KLOW, KHIGH in BDB, FRBB.
  assert (MU : munch [(BD, BD + 40); (FRB + 32, FRB + 40); (FRB + 56, FRB + 64); (FRB + 64, FRB + 72); (FRB + 104, FRB + 112)] m m)
    by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  destruct (AROS ltac:(lia)) as (US & RGS & RGSS). pose proof (DJ2 ltac:(lia)) as DJ2a. pose proof (DJ3 ltac:(lia)) as DJ3a.
  clear AROS DJ2 DJ3.
  kx_autoFLAx [KAUnp BD 40; KAUnp SEQ n; KAUnp TP 8; KAUnp T 8; KAApp BD 40; KAApp (FRB + 32) 80]
      [SQ_INL_BITINIT_L1_EXIT; SQ_INL_BITINIT_L1_ERR] 400%nat
      [KZRange n 8 (2^47 - 4096);
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 112); KZRange TP 4096 (2^47 - 8); KZRange T 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign T 4;
       KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 32) 8; KZWr (FRB + 56) 8; KZWr (FRB + 64) 8; KZWr (FRB + 104) 8;
       KZDisj (FRB + 32) 8 BD 40; KZDisj (FRB + 56) 8 BD 40; KZDisj (FRB + 64) 8 BD 40; KZDisj (FRB + 104) 8 BD 40;
       KZDisj (FRB + 32) 8 (FRB + 56) 8; KZDisj (FRB + 32) 8 (FRB + 64) 8; KZDisj (FRB + 32) 8 (FRB + 104) 8;
       KZDisj (FRB + 56) 8 (FRB + 64) 8; KZDisj (FRB + 56) 8 (FRB + 104) 8; KZDisj (FRB + 64) 8 (FRB + 104) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 32) 8 TP 8; KZDisj (FRB + 56) 8 TP 8; KZDisj (FRB + 64) 8 TP 8; KZDisj (FRB + 104) 8 TP 8;
       KZDisj BD 40 SEQ n; KZDisj (FRB + 32) 8 SEQ n; KZDisj (FRB + 56) 8 SEQ n; KZDisj (FRB + 64) 8 SEQ n; KZDisj (FRB + 104) 8 SEQ n]
      [(SEQ, n); (BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8); (TP, 8)]
      [(BD, 40); (FRB + 32, 8); (FRB + 56, 8); (FRB + 64, 8); (FRB + 104, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RGF | kx_acc RGTP | kx_acc RGT | kx_acc RGBS | kx_acc RGTPS | kx_acc RGTS | kx_acc RIMG | kx_acc RGS | kx_acc RGSS] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = SQ_INL_BITINIT_L1_EXIT) by (unfold SQ_INL_BITINIT_L1_EXIT; reflexivity)
              | assert (UPC = SQ_INL_BITINIT_L1_ERR) by (unfold SQ_INL_BITINIT_L1_ERR; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP _ _ _ => fail 99 "accP left"
    | |- sc_resid _ _ _ ?S => kx_side_pre; match goal with |- ?G => fail 99 "sc_resid left" G end
    | |- _ /\ _ /\ (?A + _ <= ?B \/ _) => fail 99 "disj left" A B
    | |- ?A /\ ?B => fail 99 "conj left" A
    | |- ?A <= ?B => fail 99 "le left"
    | |- rdn _ _ _ _ = _ => fail 99 "rdn left"
    | |- _ = _ => fail 99 "eq left"
    | |- _ => fail 99 "other goal"
  end.
  all: clear GOT RIC SHB INI LAY REAL.
  all: kx_mem.
  all: try (bi_enum BD 8).
  all: kx_abs.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        let b := eval vm_compute in (Z.eqb UPC SQ_INL_BITINIT_L1_EXIT) in
        lazymatch b with true => bi_close_ok BD n SEQ | false => bi_close_err BD end
  end.
Qed.

Theorem sq_inl_bitinit_L1_proof : sq_inl_bitinit_L1_stmt.
Proof.
  unfold sq_inl_bitinit_L1_stmt, sq_inl_bitinit_L1_stmt_if. intros until sqb. intros.
  assert (NC : Z.of_nat (length sqb) = 0 \/ Z.of_nat (length sqb) = 1 \/ Z.of_nat (length sqb) = 2 \/
              Z.of_nat (length sqb) = 3 \/ Z.of_nat (length sqb) = 4 \/ Z.of_nat (length sqb) = 5 \/
              Z.of_nat (length sqb) = 6 \/ Z.of_nat (length sqb) = 7 \/ 8 <= Z.of_nat (length sqb)) by lia.
  destruct NC as [NC|[NC|[NC|[NC|[NC|[NC|[NC|[NC|NC]]]]]]]];
    [ eapply sq_inl_bitinit_L1_c0 | eapply sq_inl_bitinit_L1_c1 | eapply sq_inl_bitinit_L1_c2 | eapply sq_inl_bitinit_L1_c3
    | eapply sq_inl_bitinit_L1_c4 | eapply sq_inl_bitinit_L1_c5 | eapply sq_inl_bitinit_L1_c6 | eapply sq_inl_bitinit_L1_c7
    | eapply sq_inl_bitinit_L1_c8 ]; eassumption.
Qed.

End CANSEC1.
