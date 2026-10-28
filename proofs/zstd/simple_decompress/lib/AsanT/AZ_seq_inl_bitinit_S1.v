From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_kx AZ_globals AZ_globalsR AZ_huf_iface AZ_seq_bit_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
Ltac kx_pull ::= kx_pull1; kx_pull1.
Ltac kx_lia ::= kx_bv_ranges; solve [kx_lia_pruned].

Section CANSEC1. Context {rc : runConstT}.

Definition sq_inl_bitinit_S1_entry : Z := 0x8f4f8.
Definition sq_inl_bitinit_S1_exit : Z := 0x8f994.
Definition sq_inl_bitinit_S1_err : Z := 0x91fa0.

Definition sq_inl_bitinit_S1_post (ra sp gp tp t0 t1 t2 s0 s2 s6 s8 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 : word) (F : bvmap 5 word) (fc : bv 32)
    (FRB BD SRC n TP NT : Z) (m : amem) : machine_state -> Prop :=
  fun ms' =>
    (exists a0 a1 a2' a3' a4' a5' a6 a7 x7 m' cw bc jpad,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FRB) a0 a1 a2' a3' a4' a5' a6 a7
                     s2 (Z_to_bv 64 SRC) (Z_to_bv 64 BD) (Z_to_bv 64 ASHOFF) s6 x7 s8 (Z_to_bv 64 TP) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 sq_inl_bitinit_S1_exit) fc None m' (seg_rom bsegs)
       /\ munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
       /\ rw_cells bsegs m' BD (sbd_cells cw bc jpad (bitd_ptr SRC n) SRC)
       /\ rw_cells bsegs m' (FRB + 24) [C8 a5; C8 a2; C8 a4] /\ rw_cells bsegs m' (FRB + 168) [C8 a3]
       /\ a0 = Z_to_bv 64 (NT + 4) /\ a1 = Z_to_bv 64 (SRC + 8) /\ a3' = Z_to_bv 64 NT
       /\ 1 <= bc <= 64 /\ (8 <= n -> bc <= 8))
    \/ (exists a0 a1 a2' a3' a4' a5' a6 a7 x7 m' bs x24 x32 x40 x168,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FRB) a0 a1 a2' a3' a4' a5' a6 a7
                     s2 (Z_to_bv 64 SRC) (Z_to_bv 64 BD) (Z_to_bv 64 ASHOFF) s6 x7 s8 (Z_to_bv 64 TP) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 sq_inl_bitinit_S1_err) fc None m' (seg_rom bsegs)
       /\ munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
       /\ rw_cells bsegs m' BD [CB 40 bs]
       /\ rw_cells bsegs m' (FRB + 24) [C8 x24; C8 x32; C8 x40] /\ rw_cells bsegs m' (FRB + 168) [C8 x168]).

Definition sq_inl_bitinit_S1_stmt : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (FRB BD SRC n TP NT : Z) (c24 c32 c40 c168 : word) (src junk : list byte),
  mem_inv bsegs m ->
  rw_cells bsegs m BD [CB 40 junk] -> BD mod 8 = 0 ->
  rw_cells bsegs m (FRB + 24) [C8 c24; C8 c32; C8 c40] -> rw_cells bsegs m (FRB + 168) [C8 c168] ->
  rw_cells bsegs m TP [C8 (Z_to_bv 64 NT)] ->
  bytes_at bsegs m SRC src -> zlen src = n -> 1 <= n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 ->
  4096 <= FRB -> FRB + 176 < 2^47 -> FRB mod 8 = 0 -> 4096 <= TP -> TP + 8 < 2^47 -> TP mod 8 = 0 ->
  4096 <= NT -> NT + 8 < 2^47 -> NT mod 4 = 0 ->
  (BD + 40 <= SRC \/ SRC + n <= BD) ->
  (BD + 40 <= FRB + 24 \/ FRB + 48 <= BD) -> (BD + 40 <= FRB + 168 \/ FRB + 176 <= BD) ->
  (FRB + 176 <= SRC \/ SRC + n <= FRB + 24) ->
  (BD + 40 <= TP \/ TP + 8 <= BD) -> (FRB + 176 <= TP \/ TP + 8 <= FRB + 24) ->
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> ahull RNG m BD 40 -> aro RNG m SRC n ->
  app_blk (FRB + 24) (FRB + 48) -> rng RNG (FRB + 24) 24 -> app_blk (FRB + 168) (FRB + 176) -> rng RNG (FRB + 168) 8 ->
  aro RNG m TP 8 -> aro RNG m NT 8 ->
  rng_aimg RNG -> art m ->
  evtF bsegs RNG (sq_inl_bitinit_S1_post ra sp gp tp t0 t1 t2 s0 s2 s6 s8 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 F fc FRB BD SRC n TP NT m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FRB) a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 SRC) (Z_to_bv 64 BD) (Z_to_bv 64 ASHOFF) s6 (Z_to_bv 64 n) s8 (Z_to_bv 64 TP) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 sq_inl_bitinit_S1_entry) fc None m (seg_rom bsegs)).

Definition sq_inl_bitinit_S1_stmt_if (CND : Z -> Prop) : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (FRB BD SRC n TP NT : Z) (c24 c32 c40 c168 : word) (src junk : list byte),
  mem_inv bsegs m ->
  rw_cells bsegs m BD [CB 40 junk] -> BD mod 8 = 0 ->
  rw_cells bsegs m (FRB + 24) [C8 c24; C8 c32; C8 c40] -> rw_cells bsegs m (FRB + 168) [C8 c168] ->
  rw_cells bsegs m TP [C8 (Z_to_bv 64 NT)] ->
  bytes_at bsegs m SRC src -> zlen src = n -> 1 <= n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 ->
  4096 <= FRB -> FRB + 176 < 2^47 -> FRB mod 8 = 0 -> 4096 <= TP -> TP + 8 < 2^47 -> TP mod 8 = 0 ->
  4096 <= NT -> NT + 8 < 2^47 -> NT mod 4 = 0 ->
  (BD + 40 <= SRC \/ SRC + n <= BD) ->
  (BD + 40 <= FRB + 24 \/ FRB + 48 <= BD) -> (BD + 40 <= FRB + 168 \/ FRB + 176 <= BD) ->
  (FRB + 176 <= SRC \/ SRC + n <= FRB + 24) ->
  (BD + 40 <= TP \/ TP + 8 <= BD) -> (FRB + 176 <= TP \/ TP + 8 <= FRB + 24) ->
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> ahull RNG m BD 40 -> aro RNG m SRC n ->
  app_blk (FRB + 24) (FRB + 48) -> rng RNG (FRB + 24) 24 -> app_blk (FRB + 168) (FRB + 176) -> rng RNG (FRB + 168) 8 ->
  aro RNG m TP 8 -> aro RNG m NT 8 ->
  rng_aimg RNG -> art m -> CND n ->
  evtF bsegs RNG (sq_inl_bitinit_S1_post ra sp gp tp t0 t1 t2 s0 s2 s6 s8 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 F fc FRB BD SRC n TP NT m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 FRB) a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 SRC) (Z_to_bv 64 BD) (Z_to_bv 64 ASHOFF) s6 (Z_to_bv 64 n) s8 (Z_to_bv 64 TP) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 sq_inl_bitinit_S1_entry) fc None m (seg_rom bsegs)).

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
  first [ match goal with H : rw_cells _ _ ?S _ |- rw_cells _ _ ?S2 _ => constr_eq S S2; exact H end
        | lazymatch goal with |- rw_cells _ ?mc ?S2 ?cs => let L := bi_bases mc tt in fail 99 "SLOT" S2 cs L end ].

Ltac bi_eq :=
  first [ reflexivity | (f_equal; lia) | (rewrite ?Z_to_bv_bv_unsigned; reflexivity)
        | match goal with |- ?G => fail 99 "EQ" G end ].

Ltac bi_ms :=
  first [ reflexivity | match goal with |- ?G => fail 99 "MS" G end ].

Ltac bi_close_ok B N S :=
  apply evtF_done;
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
    unfold sq_inl_bitinit_S1_post; left;
    first [ match goal with BDC' : rw_cells _ mc B _ |- _ => idtac end
          | let L := bi_bases mc tt in fail 99 "OK noBD" L ];
    match goal with BDC' : rw_cells _ mc B ?cs |- _ =>
      do 9 eexists; exists mc;
      first [ lazymatch cs with
              | context [C4 (Z_to_bv 64 ?v)] => eexists; exists (v mod 2^64); eexists
              | context [C4 (edenot ?E ?e)] => eexists; exists (bv_unsigned (edenot E e) mod 2^64); eexists
              end
            | fail 99 "OK noC4" cs ];
      split; [bi_ms|];
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
  do 2 (split; [bi_slot|]);
  do 3 (split; [bi_eq|]);
  first [ split; [lia|]; intros; lia
        | match goal with |- ?G => fail 99 "OK tail" G end ].

Ltac bi_close_err B :=
  apply evtF_done;
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
    unfold sq_inl_bitinit_S1_post; right;
    first [ match goal with H : rw_cells _ mc B _ |- _ => idtac end
          | let L := bi_bases mc tt in fail 99 "ERR noBD" L ];
    lazymatch goal with H : rw_cells _ mc B _ |- _ =>
      let bs := fresh "bs" in let Hbs := fresh "Hbs" in
      destruct (rw_cells_forget bsegs _ _ _ H) as [bs Hbs];
      do 9 eexists; exists mc, bs; do 4 eexists;
      split; [bi_ms|];
      first [ split; [eassumption|]; split; [eassumption|]; split; [eassumption|]
            | lazymatch goal with |- ?G1 /\ ?G2 /\ ?G3 /\ _ => fail 99 "ERR mem" G1 G2 G3 end ];
      split; [exact Hbs|]
    end
  end;
  split; [bi_slot|]; bi_slot.

Lemma sq_inl_bitinit_S1_c1 : sq_inl_bitinit_S1_stmt_if (fun n => n = 1).
Proof.
  unfold sq_inl_bitinit_S1_stmt_if, sq_inl_bitinit_S1_entry. intros until junk.
  intros MI HBD BD8 H24 H168 HTP SB LEN N1 R1 R2 R3 R4 R5 R6 A1 R7 R8 A2 R9 R10 A3 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6
         APB AROB AHB AROS AP24 RG24 AP168 RG168 AROTP ARONT RIMG ART C.
  cbv beta in C. clear AHB.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct ARONT as (UNT & RGNT & RGNTS).
  destruct AROS as (US & RGS & RGSS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (F24B : FRB + 48 <= KLOW \/ KHIGH <= FRB + 24) by (unfold app_blk in AP24; clear - AP24; lia).
  assert (F168B : FRB + 176 <= KLOW \/ KHIGH <= FRB + 168) by (unfold app_blk in AP168; clear - AP168; lia).
  unfold KLOW, KHIGH in BDB, F24B, F168B.
  assert (MU : munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLAx [KAUnp BD 40; KAUnp SRC n; KAUnp TP 8; KAUnp NT 8; KAApp BD 40; KAApp (FRB + 24) 24; KAApp (FRB + 168) 8]
      [sq_inl_bitinit_S1_exit; sq_inl_bitinit_S1_err] 400%nat
      [KZRange n 1 1;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 176); KZRange TP 4096 (2^47 - 8); KZRange NT 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign NT 4;
       KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 24) 24; KZWr (FRB + 168) 8;
       KZDisj (FRB + 24) 24 BD 40; KZDisj (FRB + 168) 8 BD 40; KZDisj (FRB + 24) 24 (FRB + 168) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 24) 24 TP 8; KZDisj (FRB + 168) 8 TP 8;
       KZDisj BD 40 SRC n; KZDisj (FRB + 24) 24 SRC n; KZDisj (FRB + 168) 8 SRC n]
      [(SRC, n); (BD, 40); (FRB + 24, 24); (FRB + 168, 8); (TP, 8)]
      [(BD, 40); (FRB + 24, 24); (FRB + 168, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RG24 | kx_acc RG168 | kx_acc RGTP | kx_acc RGS | kx_acc RGBS | kx_acc RGTPS | kx_acc RGNT | kx_acc RGNTS | kx_acc RGSS | kx_acc RIMG] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = sq_inl_bitinit_S1_exit) by (unfold sq_inl_bitinit_S1_exit; reflexivity)
              | assert (UPC = sq_inl_bitinit_S1_err) by (unfold sq_inl_bitinit_S1_err; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP ?E _ (?a, ?k) => fail 99 "accP left" a k
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
        let b := eval vm_compute in (Z.eqb UPC sq_inl_bitinit_S1_exit) in
        lazymatch b with true => bi_close_ok BD n SRC | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_S1_c2 : sq_inl_bitinit_S1_stmt_if (fun n => n = 2).
Proof.
  unfold sq_inl_bitinit_S1_stmt_if, sq_inl_bitinit_S1_entry. intros until junk.
  intros MI HBD BD8 H24 H168 HTP SB LEN N1 R1 R2 R3 R4 R5 R6 A1 R7 R8 A2 R9 R10 A3 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6
         APB AROB AHB AROS AP24 RG24 AP168 RG168 AROTP ARONT RIMG ART C.
  cbv beta in C. clear AHB.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct ARONT as (UNT & RGNT & RGNTS).
  destruct AROS as (US & RGS & RGSS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (F24B : FRB + 48 <= KLOW \/ KHIGH <= FRB + 24) by (unfold app_blk in AP24; clear - AP24; lia).
  assert (F168B : FRB + 176 <= KLOW \/ KHIGH <= FRB + 168) by (unfold app_blk in AP168; clear - AP168; lia).
  unfold KLOW, KHIGH in BDB, F24B, F168B.
  assert (MU : munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SRC n; KAUnp TP 8; KAUnp NT 8; KAApp BD 40; KAApp (FRB + 24) 24; KAApp (FRB + 168) 8]
      [sq_inl_bitinit_S1_exit; sq_inl_bitinit_S1_err] 400%nat
      [KZRange n 2 2; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 176); KZRange TP 4096 (2^47 - 8); KZRange NT 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign NT 4;
       KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 24) 24; KZWr (FRB + 168) 8;
       KZDisj (FRB + 24) 24 BD 40; KZDisj (FRB + 168) 8 BD 40; KZDisj (FRB + 24) 24 (FRB + 168) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 24) 24 TP 8; KZDisj (FRB + 168) 8 TP 8;
       KZDisj BD 40 SRC n; KZDisj (FRB + 24) 24 SRC n; KZDisj (FRB + 168) 8 SRC n]
      [(SRC, n); (BD, 40); (FRB + 24, 24); (FRB + 168, 8); (TP, 8)]
      [(BD, 40); (FRB + 24, 24); (FRB + 168, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RG24 | kx_acc RG168 | kx_acc RGTP | kx_acc RGS | kx_acc RGBS | kx_acc RGTPS | kx_acc RGNT | kx_acc RGNTS | kx_acc RGSS | kx_acc RIMG] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = sq_inl_bitinit_S1_exit) by (unfold sq_inl_bitinit_S1_exit; reflexivity)
              | assert (UPC = sq_inl_bitinit_S1_err) by (unfold sq_inl_bitinit_S1_err; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP ?E _ (?a, ?k) => fail 99 "accP left" a k
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
        let b := eval vm_compute in (Z.eqb UPC sq_inl_bitinit_S1_exit) in
        lazymatch b with true => bi_close_ok BD n SRC | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_S1_c3 : sq_inl_bitinit_S1_stmt_if (fun n => n = 3).
Proof.
  unfold sq_inl_bitinit_S1_stmt_if, sq_inl_bitinit_S1_entry. intros until junk.
  intros MI HBD BD8 H24 H168 HTP SB LEN N1 R1 R2 R3 R4 R5 R6 A1 R7 R8 A2 R9 R10 A3 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6
         APB AROB AHB AROS AP24 RG24 AP168 RG168 AROTP ARONT RIMG ART C.
  cbv beta in C. clear AHB.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct ARONT as (UNT & RGNT & RGNTS).
  destruct AROS as (US & RGS & RGSS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (F24B : FRB + 48 <= KLOW \/ KHIGH <= FRB + 24) by (unfold app_blk in AP24; clear - AP24; lia).
  assert (F168B : FRB + 176 <= KLOW \/ KHIGH <= FRB + 168) by (unfold app_blk in AP168; clear - AP168; lia).
  unfold KLOW, KHIGH in BDB, F24B, F168B.
  assert (MU : munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SRC n; KAUnp TP 8; KAUnp NT 8; KAApp BD 40; KAApp (FRB + 24) 24; KAApp (FRB + 168) 8]
      [sq_inl_bitinit_S1_exit; sq_inl_bitinit_S1_err] 400%nat
      [KZRange n 3 3; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 176); KZRange TP 4096 (2^47 - 8); KZRange NT 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign NT 4;
       KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 24) 24; KZWr (FRB + 168) 8;
       KZDisj (FRB + 24) 24 BD 40; KZDisj (FRB + 168) 8 BD 40; KZDisj (FRB + 24) 24 (FRB + 168) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 24) 24 TP 8; KZDisj (FRB + 168) 8 TP 8;
       KZDisj BD 40 SRC n; KZDisj (FRB + 24) 24 SRC n; KZDisj (FRB + 168) 8 SRC n]
      [(SRC, n); (BD, 40); (FRB + 24, 24); (FRB + 168, 8); (TP, 8)]
      [(BD, 40); (FRB + 24, 24); (FRB + 168, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RG24 | kx_acc RG168 | kx_acc RGTP | kx_acc RGS | kx_acc RGBS | kx_acc RGTPS | kx_acc RGNT | kx_acc RGNTS | kx_acc RGSS | kx_acc RIMG] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = sq_inl_bitinit_S1_exit) by (unfold sq_inl_bitinit_S1_exit; reflexivity)
              | assert (UPC = sq_inl_bitinit_S1_err) by (unfold sq_inl_bitinit_S1_err; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP ?E _ (?a, ?k) => fail 99 "accP left" a k
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
        let b := eval vm_compute in (Z.eqb UPC sq_inl_bitinit_S1_exit) in
        lazymatch b with true => bi_close_ok BD n SRC | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_S1_c4 : sq_inl_bitinit_S1_stmt_if (fun n => n = 4).
Proof.
  unfold sq_inl_bitinit_S1_stmt_if, sq_inl_bitinit_S1_entry. intros until junk.
  intros MI HBD BD8 H24 H168 HTP SB LEN N1 R1 R2 R3 R4 R5 R6 A1 R7 R8 A2 R9 R10 A3 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6
         APB AROB AHB AROS AP24 RG24 AP168 RG168 AROTP ARONT RIMG ART C.
  cbv beta in C. clear AHB.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct ARONT as (UNT & RGNT & RGNTS).
  destruct AROS as (US & RGS & RGSS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (F24B : FRB + 48 <= KLOW \/ KHIGH <= FRB + 24) by (unfold app_blk in AP24; clear - AP24; lia).
  assert (F168B : FRB + 176 <= KLOW \/ KHIGH <= FRB + 168) by (unfold app_blk in AP168; clear - AP168; lia).
  unfold KLOW, KHIGH in BDB, F24B, F168B.
  assert (MU : munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SRC n; KAUnp TP 8; KAUnp NT 8; KAApp BD 40; KAApp (FRB + 24) 24; KAApp (FRB + 168) 8]
      [sq_inl_bitinit_S1_exit; sq_inl_bitinit_S1_err] 400%nat
      [KZRange n 4 4; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 176); KZRange TP 4096 (2^47 - 8); KZRange NT 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign NT 4;
       KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 24) 24; KZWr (FRB + 168) 8;
       KZDisj (FRB + 24) 24 BD 40; KZDisj (FRB + 168) 8 BD 40; KZDisj (FRB + 24) 24 (FRB + 168) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 24) 24 TP 8; KZDisj (FRB + 168) 8 TP 8;
       KZDisj BD 40 SRC n; KZDisj (FRB + 24) 24 SRC n; KZDisj (FRB + 168) 8 SRC n]
      [(SRC, n); (BD, 40); (FRB + 24, 24); (FRB + 168, 8); (TP, 8)]
      [(BD, 40); (FRB + 24, 24); (FRB + 168, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RG24 | kx_acc RG168 | kx_acc RGTP | kx_acc RGS | kx_acc RGBS | kx_acc RGTPS | kx_acc RGNT | kx_acc RGNTS | kx_acc RGSS | kx_acc RIMG] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = sq_inl_bitinit_S1_exit) by (unfold sq_inl_bitinit_S1_exit; reflexivity)
              | assert (UPC = sq_inl_bitinit_S1_err) by (unfold sq_inl_bitinit_S1_err; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP ?E _ (?a, ?k) => fail 99 "accP left" a k
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
        let b := eval vm_compute in (Z.eqb UPC sq_inl_bitinit_S1_exit) in
        lazymatch b with true => bi_close_ok BD n SRC | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_S1_c5 : sq_inl_bitinit_S1_stmt_if (fun n => n = 5).
Proof.
  unfold sq_inl_bitinit_S1_stmt_if, sq_inl_bitinit_S1_entry. intros until junk.
  intros MI HBD BD8 H24 H168 HTP SB LEN N1 R1 R2 R3 R4 R5 R6 A1 R7 R8 A2 R9 R10 A3 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6
         APB AROB AHB AROS AP24 RG24 AP168 RG168 AROTP ARONT RIMG ART C.
  cbv beta in C. clear AHB.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct ARONT as (UNT & RGNT & RGNTS).
  destruct AROS as (US & RGS & RGSS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (F24B : FRB + 48 <= KLOW \/ KHIGH <= FRB + 24) by (unfold app_blk in AP24; clear - AP24; lia).
  assert (F168B : FRB + 176 <= KLOW \/ KHIGH <= FRB + 168) by (unfold app_blk in AP168; clear - AP168; lia).
  unfold KLOW, KHIGH in BDB, F24B, F168B.
  assert (MU : munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SRC n; KAUnp TP 8; KAUnp NT 8; KAApp BD 40; KAApp (FRB + 24) 24; KAApp (FRB + 168) 8]
      [sq_inl_bitinit_S1_exit; sq_inl_bitinit_S1_err] 400%nat
      [KZRange n 5 5; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 176); KZRange TP 4096 (2^47 - 8); KZRange NT 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign NT 4;
       KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 24) 24; KZWr (FRB + 168) 8;
       KZDisj (FRB + 24) 24 BD 40; KZDisj (FRB + 168) 8 BD 40; KZDisj (FRB + 24) 24 (FRB + 168) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 24) 24 TP 8; KZDisj (FRB + 168) 8 TP 8;
       KZDisj BD 40 SRC n; KZDisj (FRB + 24) 24 SRC n; KZDisj (FRB + 168) 8 SRC n]
      [(SRC, n); (BD, 40); (FRB + 24, 24); (FRB + 168, 8); (TP, 8)]
      [(BD, 40); (FRB + 24, 24); (FRB + 168, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RG24 | kx_acc RG168 | kx_acc RGTP | kx_acc RGS | kx_acc RGBS | kx_acc RGTPS | kx_acc RGNT | kx_acc RGNTS | kx_acc RGSS | kx_acc RIMG] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = sq_inl_bitinit_S1_exit) by (unfold sq_inl_bitinit_S1_exit; reflexivity)
              | assert (UPC = sq_inl_bitinit_S1_err) by (unfold sq_inl_bitinit_S1_err; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP ?E _ (?a, ?k) => fail 99 "accP left" a k
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
        let b := eval vm_compute in (Z.eqb UPC sq_inl_bitinit_S1_exit) in
        lazymatch b with true => bi_close_ok BD n SRC | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_S1_c6 : sq_inl_bitinit_S1_stmt_if (fun n => n = 6).
Proof.
  unfold sq_inl_bitinit_S1_stmt_if, sq_inl_bitinit_S1_entry. intros until junk.
  intros MI HBD BD8 H24 H168 HTP SB LEN N1 R1 R2 R3 R4 R5 R6 A1 R7 R8 A2 R9 R10 A3 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6
         APB AROB AHB AROS AP24 RG24 AP168 RG168 AROTP ARONT RIMG ART C.
  cbv beta in C. clear AHB.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct ARONT as (UNT & RGNT & RGNTS).
  destruct AROS as (US & RGS & RGSS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (F24B : FRB + 48 <= KLOW \/ KHIGH <= FRB + 24) by (unfold app_blk in AP24; clear - AP24; lia).
  assert (F168B : FRB + 176 <= KLOW \/ KHIGH <= FRB + 168) by (unfold app_blk in AP168; clear - AP168; lia).
  unfold KLOW, KHIGH in BDB, F24B, F168B.
  assert (MU : munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SRC n; KAUnp TP 8; KAUnp NT 8; KAApp BD 40; KAApp (FRB + 24) 24; KAApp (FRB + 168) 8]
      [sq_inl_bitinit_S1_exit; sq_inl_bitinit_S1_err] 400%nat
      [KZRange n 6 6; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 176); KZRange TP 4096 (2^47 - 8); KZRange NT 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign NT 4;
       KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 24) 24; KZWr (FRB + 168) 8;
       KZDisj (FRB + 24) 24 BD 40; KZDisj (FRB + 168) 8 BD 40; KZDisj (FRB + 24) 24 (FRB + 168) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 24) 24 TP 8; KZDisj (FRB + 168) 8 TP 8;
       KZDisj BD 40 SRC n; KZDisj (FRB + 24) 24 SRC n; KZDisj (FRB + 168) 8 SRC n]
      [(SRC, n); (BD, 40); (FRB + 24, 24); (FRB + 168, 8); (TP, 8)]
      [(BD, 40); (FRB + 24, 24); (FRB + 168, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RG24 | kx_acc RG168 | kx_acc RGTP | kx_acc RGS | kx_acc RGBS | kx_acc RGTPS | kx_acc RGNT | kx_acc RGNTS | kx_acc RGSS | kx_acc RIMG] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = sq_inl_bitinit_S1_exit) by (unfold sq_inl_bitinit_S1_exit; reflexivity)
              | assert (UPC = sq_inl_bitinit_S1_err) by (unfold sq_inl_bitinit_S1_err; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP ?E _ (?a, ?k) => fail 99 "accP left" a k
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
        let b := eval vm_compute in (Z.eqb UPC sq_inl_bitinit_S1_exit) in
        lazymatch b with true => bi_close_ok BD n SRC | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_S1_c7 : sq_inl_bitinit_S1_stmt_if (fun n => n = 7).
Proof.
  unfold sq_inl_bitinit_S1_stmt_if, sq_inl_bitinit_S1_entry. intros until junk.
  intros MI HBD BD8 H24 H168 HTP SB LEN N1 R1 R2 R3 R4 R5 R6 A1 R7 R8 A2 R9 R10 A3 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6
         APB AROB AHB AROS AP24 RG24 AP168 RG168 AROTP ARONT RIMG ART C.
  cbv beta in C. clear AHB.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct ARONT as (UNT & RGNT & RGNTS).
  destruct AROS as (US & RGS & RGSS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (F24B : FRB + 48 <= KLOW \/ KHIGH <= FRB + 24) by (unfold app_blk in AP24; clear - AP24; lia).
  assert (F168B : FRB + 176 <= KLOW \/ KHIGH <= FRB + 168) by (unfold app_blk in AP168; clear - AP168; lia).
  unfold KLOW, KHIGH in BDB, F24B, F168B.
  assert (MU : munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLAx_v 8 [KAUnp BD 40; KAUnp SRC n; KAUnp TP 8; KAUnp NT 8; KAApp BD 40; KAApp (FRB + 24) 24; KAApp (FRB + 168) 8]
      [sq_inl_bitinit_S1_exit; sq_inl_bitinit_S1_err] 400%nat
      [KZRange n 7 7; KZImg b_ro_lo b_ro_hi;
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 176); KZRange TP 4096 (2^47 - 8); KZRange NT 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign NT 4;
       KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 24) 24; KZWr (FRB + 168) 8;
       KZDisj (FRB + 24) 24 BD 40; KZDisj (FRB + 168) 8 BD 40; KZDisj (FRB + 24) 24 (FRB + 168) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 24) 24 TP 8; KZDisj (FRB + 168) 8 TP 8;
       KZDisj BD 40 SRC n; KZDisj (FRB + 24) 24 SRC n; KZDisj (FRB + 168) 8 SRC n]
      [(SRC, n); (BD, 40); (FRB + 24, 24); (FRB + 168, 8); (TP, 8)]
      [(BD, 40); (FRB + 24, 24); (FRB + 168, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RG24 | kx_acc RG168 | kx_acc RGTP | kx_acc RGS | kx_acc RGBS | kx_acc RGTPS | kx_acc RGNT | kx_acc RGNTS | kx_acc RGSS | kx_acc RIMG] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = sq_inl_bitinit_S1_exit) by (unfold sq_inl_bitinit_S1_exit; reflexivity)
              | assert (UPC = sq_inl_bitinit_S1_err) by (unfold sq_inl_bitinit_S1_err; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP ?E _ (?a, ?k) => fail 99 "accP left" a k
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
        let b := eval vm_compute in (Z.eqb UPC sq_inl_bitinit_S1_exit) in
        lazymatch b with true => bi_close_ok BD n SRC | false => bi_close_err BD end
  end.
Qed.

Lemma sq_inl_bitinit_S1_c8 : sq_inl_bitinit_S1_stmt_if (fun n => 8 <= n).
Proof.
  unfold sq_inl_bitinit_S1_stmt_if, sq_inl_bitinit_S1_entry. intros until junk.
  intros MI HBD BD8 H24 H168 HTP SB LEN N1 R1 R2 R3 R4 R5 R6 A1 R7 R8 A2 R9 R10 A3 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6
         APB AROB AHB AROS AP24 RG24 AP168 RG168 AROTP ARONT RIMG ART C.
  cbv beta in C. clear AHB.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AROB as (UB & RGB & RGBS). destruct AROTP as (UTP & RGTP & RGTPS). destruct ARONT as (UNT & RGNT & RGNTS).
  destruct AROS as (US & RGS & RGSS).
  assert (BDB : BD + 40 <= KLOW \/ KHIGH <= BD) by (unfold app_blk in APB; clear - APB; lia).
  assert (F24B : FRB + 48 <= KLOW \/ KHIGH <= FRB + 24) by (unfold app_blk in AP24; clear - AP24; lia).
  assert (F168B : FRB + 176 <= KLOW \/ KHIGH <= FRB + 168) by (unfold app_blk in AP168; clear - AP168; lia).
  unfold KLOW, KHIGH in BDB, F24B, F168B.
  assert (MU : munch [(BD, BD + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  kx_autoFLAx [KAUnp BD 40; KAUnp SRC n; KAUnp TP 8; KAUnp NT 8; KAApp BD 40; KAApp (FRB + 24) 24; KAApp (FRB + 168) 8]
      [sq_inl_bitinit_S1_exit; sq_inl_bitinit_S1_err] 400%nat
      [KZRange n 8 (2^47 - 4096);
       KZRange BD 4096 (2^47 - 40); KZRange FRB 4096 (2^47 - 176); KZRange TP 4096 (2^47 - 8); KZRange NT 4096 (2^47 - 8);
       KZAlign BD 8; KZAlign FRB 8; KZAlign TP 8; KZAlign NT 4;
       KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZWr BD 40; KZWr (FRB + 24) 24; KZWr (FRB + 168) 8;
       KZDisj (FRB + 24) 24 BD 40; KZDisj (FRB + 168) 8 BD 40; KZDisj (FRB + 24) 24 (FRB + 168) 8;
       KZDisj BD 40 TP 8; KZDisj (FRB + 24) 24 TP 8; KZDisj (FRB + 168) 8 TP 8;
       KZDisj BD 40 SRC n; KZDisj (FRB + 24) 24 SRC n; KZDisj (FRB + 168) 8 SRC n]
      [(SRC, n); (BD, 40); (FRB + 24, 24); (FRB + 168, 8); (TP, 8)]
      [(BD, 40); (FRB + 24, 24); (FRB + 168, 8)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGB | kx_acc RG24 | kx_acc RG168 | kx_acc RGTP | kx_acc RGS | kx_acc RGBS | kx_acc RGTPS | kx_acc RGNT | kx_acc RGNTS | kx_acc RGSS | kx_acc RIMG] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) =>
        first [ assert (UPC = sq_inl_bitinit_S1_exit) by (unfold sq_inl_bitinit_S1_exit; reflexivity)
              | assert (UPC = sq_inl_bitinit_S1_err) by (unfold sq_inl_bitinit_S1_err; reflexivity)
              | fail 99 "LEAF pc" UPC ]
    | |- evtF _ _ _ _ => fail 99 "evtF other"
    | |- accP ?E _ (?a, ?k) => fail 99 "accP left" a k
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
        let b := eval vm_compute in (Z.eqb UPC sq_inl_bitinit_S1_exit) in
        lazymatch b with true => bi_close_ok BD n SRC | false => bi_close_err BD end
  end.
Qed.

Theorem sq_inl_bitinit_S1_proof : sq_inl_bitinit_S1_stmt.
Proof.
  unfold sq_inl_bitinit_S1_stmt. intros until junk. intros.
  assert (NC : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ 8 <= n) by lia.
  destruct NC as [NC|[NC|[NC|[NC|[NC|[NC|[NC|NC]]]]]]];
    [ eapply sq_inl_bitinit_S1_c1 | eapply sq_inl_bitinit_S1_c2 | eapply sq_inl_bitinit_S1_c3 | eapply sq_inl_bitinit_S1_c4
    | eapply sq_inl_bitinit_S1_c5 | eapply sq_inl_bitinit_S1_c6 | eapply sq_inl_bitinit_S1_c7 | eapply sq_inl_bitinit_S1_c8 ];
    eassumption.
Qed.

End CANSEC1.
