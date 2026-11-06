(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Pj_loc_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition OSS_CTOR : Z := 0x3f1f4.
Definition OSS_SB_CTOR : Z := 0x41e6c.
Definition OSS_INIT_BUF : Z := 0x41f34.
Definition OSS_IOS_INIT : Z := 0x78f34.
Definition OSS_PUT : Z := 0x41a18.
Definition OSS_PADOUT : Z := 0x41bc0.
Definition OSS_XSPUTN : Z := 0x7a104.
Definition OSS_OVERFLOW : Z := 0x7acd8.
Definition OSS_PUSH_BACK : Z := 0x75768.
Definition OSS_APPEND : Z := 0x758b4.
Definition OSS_RESIZE : Z := 0x75b9c.
Definition OSS_STR : Z := 0x7aafc.
Definition OSS_IOS_DTOR : Z := 0x79ef8.
Definition OSS_OPNEW : Z := 0xcf4c4.
Definition OSS_OPDEL_SZ : Z := 0x73638.
Definition OSS_MEMMOVE : Z := 0xca990.
Definition OSS_MEMSET : Z := 0xcab0c.

Definition OSS_OS_VPTR : Z := 0xd3fc8.
Definition OSS_OS_CVPTR : Z := 0xd4038.
Definition OSS_SB_VPTR : Z := 0xd3e38.
Definition OSS_SBB_VPTR : Z := 0xd3bf8.
Definition OSS_IOS_VPTR : Z := 0xd3ff0.
Definition OSS_IOS_CVPTR : Z := 0xd4060.
Definition OSS_IOSB_VPTR : Z := 0xd3b30.
Definition OSS_CLASSIC : Z := 0xe8bd8.
Definition OSS_GOT_VT : Z := 0xd6530.
Definition OSS_VTT : Z := 0xd4000.
Definition OSS_VBOFF : Z := 0xd3fb0.
Definition OSS_SBVT : Z := 0xd3e98.

Definition imp_vt_rows (m : mem) : Prop :=
  rw_cells psegs m OSS_GOT_VT [C8 (Z_to_bv 64 OSS_VTT); C8 (Z_to_bv 64 (OSS_SB_VPTR - 16)); C8 (Z_to_bv 64 (OSS_SBB_VPTR - 16)); C8 (Z_to_bv 64 OSS_VBOFF)]
  /\ rw_cells psegs m OSS_VTT [C8 (Z_to_bv 64 OSS_OS_VPTR); C8 (Z_to_bv 64 OSS_OS_CVPTR); C8 (Z_to_bv 64 OSS_IOS_CVPTR); C8 (Z_to_bv 64 OSS_IOS_VPTR); C8 (Z_to_bv 64 0x70)]
  /\ rw_cells psegs m OSS_VBOFF [C8 (Z_to_bv 64 0x70)]
  /\ rw_cells psegs m OSS_SBVT [C8 (Z_to_bv 64 OSS_XSPUTN); C8 (Z_to_bv 64 OSS_OVERFLOW)].

Lemma signed_lit : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit by lia.
  destruct (Z.ltb_spec x (2^63)); lia.
Qed.

Lemma imp_vt_rows_transport : forall W m m', imp_vt_rows m -> munch W m m' -> wmono psegs m m' ->
  (disjoint_from W 0xd3000 0x4000) -> imp_vt_rows m'.
Proof.
  intros W m m' (V1 & V2 & V3 & V4) MU WM D.
  assert (DS : forall A n, 0xd3000 <= A -> A + Z.of_nat n <= 0xd7000 -> disjoint_from W A (Z.of_nat n)).
  { intros A n HA HB. clear - D HA HB. induction W as [|[lo hi] W IH]; [exact I|]. destruct D as [D1 D2]. split; [cbn in *; lia| exact (IH D2)]. }
  unfold imp_vt_rows, OSS_GOT_VT, OSS_VTT, OSS_VBOFF, OSS_SBVT in *.
  repeat split; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply DS; cbn; lia]).
Qed.

Definition OSS_PB_STACK : Z := 64 + 16 + RMALLOC_STACK.
Definition OSS_OV_STACK : Z := 80 + OSS_PB_STACK.
Definition OSS_XSPUTN_STACK : Z := 64 + OSS_OV_STACK.
Definition OSS_PUT_STACK : Z := 96 + 96 + OSS_XSPUTN_STACK.
Definition OSS_CTOR_STACK : Z := 224.
Definition OSS_STR_STACK : Z := 64 + 16 + RMALLOC_STACK.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Record ossst : Type := mkOss { os_data : Z; os_cap : Z; os_blk : option bptr; os_fuel : nat; os_w : Z }.

Definition os_lim (st : ossst) : Z := match os_blk st with None => 22 | Some _ => os_cap st - 1 end.

Definition os_ch (st : ossst) : @chst bptr := (os_fuel st, os_cap st, os_blk st).

Definition os_k (st : ossst) : Z := Z.of_nat PJ_FUEL - Z.of_nat (os_fuel st).

Definition osblocks (st : ossst) : list block :=
  match os_blk st with Some b => [(b, os_data st, os_cap st)] | None => [] end.

Definition oss0 (O : Z) : ossst := mkOss (O + 73) IMP_SCAP0 None PJ_FUEL 0.

Definition os_grown (st : ossst) (b : bptr) (NEW : Z) : ossst :=
  mkOss NEW (2 * os_cap st) (Some b) (Nat.pred (os_fuel st)) (os_w st + 1).

Definition os_adv (st : ossst) (n : Z) : ossst := mkOss (os_data st) (os_cap st) (os_blk st) (os_fuel st) (os_w st + n).

Definition STRREP (m : mem) (O : Z) (st : ossst) : Prop :=
  match os_blk st with
  | None => rw_cells psegs m (O + 72) [C1 (Z_to_bv 8 44)]
            /\ (exists bs, rw_cells psegs m (O + 73) [CB 23 bs])
            /\ os_data st = O + 73
  | Some b => rw_cells psegs m (O + 72) [C8 (Z_to_bv 64 (os_cap st + 1)); C8 (Z_to_bv 64 (os_cap st - 1)); C8 (Z_to_bv 64 (os_data st))]
            /\ (exists bs, rw_cells psegs m (os_data st) [CB (Z.to_nat (os_cap st)) bs])
            /\ rblock_range (os_data st) (os_cap st)
  end.

Definition sb_cellsI (st : ossst) : list cell :=
  [C8 (Z_to_bv 64 OSS_SB_VPTR); C8 (Z_to_bv 64 OSS_CLASSIC);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 (os_data st)); C8 (Z_to_bv 64 (os_data st + os_w st)); C8 (Z_to_bv 64 (os_data st + os_lim st))].

Definition mode16 : list byte := [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].

Definition PUTCELLS (m : mem) (O : Z) (st : ossst) : Prop :=
  rw_cells psegs m (O + 8) (sb_cellsI st)
  /\ (exists hm, rw_cells psegs m (O + 96) [C8 (Z_to_bv 64 hm)] /\ os_data st <= hm <= os_data st + os_w st)
  /\ (exists j108, rw_cells psegs m (O + 104) [CB 4 mode16; CB 4 j108]).

Definition OSNUM (len : Z) (st : ossst) : Prop :=
  0 <= os_w st <= os_lim st /\ (os_fuel st <= PJ_FUEL)%nat /\ 24 * 2 ^ (os_k st) <= os_cap st <= PJ_CAPMAX len
  /\ match os_blk st with None => os_cap st = IMP_SCAP0 /\ os_fuel st = PJ_FUEL | Some _ => os_cap st mod 16 = 0 end.

Definition SBINV (m : mem) (O len : Z) (st : ossst) : Prop := PUTCELLS m O st /\ STRREP m O st /\ OSNUM len st.

Definition ios_cellsI (O fill : Z) (j124 j260 : list byte) : list cell :=
  [C8 (Z_to_bv 64 OSS_IOS_VPTR);
   C4 (Z_to_bv 64 0x1002); CB 4 j124;
   C8 (Z_to_bv 64 6); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 (O + 8)); C8 (Z_to_bv 64 OSS_CLASSIC);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 fill); CB 4 j260].

Lemma ios_cellsI_size : forall O fill j124 j260, cells_size (ios_cellsI O fill j124 j260) = 152%nat.
Proof. intros. reflexivity. Qed.
Lemma sb_cellsI_size : forall st, cells_size (sb_cellsI st) = 64%nat.
Proof. intros. reflexivity. Qed.

Definition IOSINV (m : mem) (O fill : Z) : Prop :=
  rw_cells psegs m O [C8 (Z_to_bv 64 OSS_OS_VPTR)] /\ exists j124 j260, rw_cells psegs m (O + 112) (ios_cellsI O fill j124 j260).

Definition OSSINV (m : mem) (O len : Z) (st : ossst) (fill : Z) : Prop := SBINV m O len st /\ IOSINV m O fill.

Lemma os_k_range : forall st, (os_fuel st <= PJ_FUEL)%nat -> 0 <= os_k st <= 24.
Proof. intros st H. unfold os_k, PJ_FUEL in *. lia. Qed.

Lemma OSNUM_fuel : forall len st, 0 <= len <= SJ_PADMAX -> OSNUM len st -> exists f, os_fuel st = S f.
Proof.
  intros len st HL (_ & HF & HC & _).
  pose proof (os_k_range st HF) as K.
  assert (K23 : os_k st < 23) by (eapply (schain_fuel len (os_cap st)); [exact HL| lia| apply HC| apply HC]).
  unfold os_k, PJ_FUEL in *. destruct (os_fuel st) as [|f]; [cbn in K23; lia| exists f; reflexivity].
Qed.

Lemma OSNUM_cap24 : forall len st, OSNUM len st -> 24 <= os_cap st.
Proof.
  intros len st (_ & HF & HC & _). pose proof (os_k_range st HF) as K.
  assert (0 < 2 ^ os_k st) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma os_grow_ok : forall len st more, 0 <= len -> OSNUM len st -> os_w st = os_lim st -> 1 <= more ->
  os_w st + more <= PJ_OUTMAX len -> chain_ok len (os_cap st) (2 * os_cap st) = true.
Proof.
  intros len st more HL NUM FULL M1 HB. apply chain_ok_spec. unfold PJ_CAPMAX.
  pose proof (OSNUM_cap24 len st NUM) as C24. pose proof (PJ_OUTMAX_pos len HL) as P4.
  destruct NUM as (_ & _ & _ & HB2). unfold os_lim in FULL. unfold IMP_SCAP0 in HB2. destruct (os_blk st); lia.
Qed.

Lemma OSNUM_grown : forall len st b NEW f, 0 <= len <= SJ_PADMAX -> OSNUM len st -> os_fuel st = S f -> os_w st = os_lim st ->
  chain_ok len (os_cap st) (2 * os_cap st) = true -> OSNUM len (os_grown st b NEW).
Proof.
  intros len st b NEW f HL NUM EF FULL OK. pose proof (OSNUM_cap24 len st NUM) as C24. destruct NUM as (HW & HF & HC & HB). apply chain_ok_spec in OK.
  unfold OSNUM, os_grown, os_lim, os_k in *. cbn [os_w os_blk os_cap os_fuel os_data] in *.
  rewrite EF in *. cbn [Nat.pred]. unfold IMP_SCAP0 in HB.
  split; [destruct (os_blk st); lia|]. split; [lia|]. split; [| destruct (os_blk st); lia].
  split; [| lia].
  replace (Z.of_nat PJ_FUEL - Z.of_nat f) with (Z.succ (Z.of_nat PJ_FUEL - Z.of_nat (S f))) by lia.
  rewrite Z.pow_succ_r by lia. lia.
Qed.

Lemma OSNUM_adv : forall len st n, OSNUM len st -> 0 <= n -> os_w st + n <= os_lim st -> OSNUM len (os_adv st n).
Proof.
  intros len st n (HW & HF & HC & HB) H0 H1. unfold OSNUM, os_adv, os_lim, os_k in *. cbn [os_w os_blk os_cap os_fuel os_data] in *.
  split; [lia|]. split; [exact HF|]. split; [exact HC| exact HB].
Qed.

Definition pb_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (O len : Z) (st : ossst) (m : mem)
    (b : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (NEW : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo q /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((b, NEW, 2 * os_cap st) :: LB0) m'
    /\ rw_cells psegs m' (O + 72) [C8 (Z_to_bv 64 (2 * os_cap st + 1)); C8 (Z_to_bv 64 (os_lim st + 1)); C8 (Z_to_bv 64 NEW)]
    /\ (exists bs, rw_cells psegs m' NEW [CB (Z.to_nat (2 * os_cap st)) bs])
    /\ rblock_range NEW (2 * os_cap st) /\ (2 * os_cap st) mod 16 = 0
    /\ lx_pres LB0 q [(O + 72, O + 96)] m m'.

Definition push_back_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
         (O len : Z) (st : ossst),
  RHEAP s (osblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
  stk psegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - OSS_PB_STACK ->
  rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m ->
  q <= O -> O + 264 <= B ->
  0 <= len <= SJ_PADMAX -> STRREP m O st -> OSNUM len st -> os_w st = os_lim st ->
  chain_ok len (os_cap st) (2 * os_cap st) = true ->
  implM psegs (pj_grow1 raw_malloc raw_free ps_so set_so_ps (2 * os_cap st) (os_blk st)) s
        (pb_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B O len st m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (O + 72)) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 OSS_PUSH_BACK) fc None m (seg_rom psegs)).

Definition ov_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (O len c : Z) (st : ossst) (m : mem)
    (ch : @chst bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (b : bptr) (NEW : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo q /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ ch = os_ch (os_grown st b NEW)
    /\ RHEAP s' (osblocks (os_grown st b NEW) ++ LB0) m'
    /\ SBINV m' O len (os_grown st b NEW)
    /\ lx_pres LB0 q [(O + 8, O + 112)] m m'.

Definition overflow_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
         (O len c : Z) (st : ossst) (f : nat),
  RHEAP s (osblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
  stk psegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - OSS_OV_STACK ->
  rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m ->
  q <= O -> O + 264 <= B ->
  0 <= len <= SJ_PADMAX -> SBINV m O len st -> os_w st = os_lim st -> os_fuel st = S f -> 0 <= c < 256 ->
  chain_ok len (os_cap st) (2 * os_cap st) = true ->
  implM psegs (pj_part raw_malloc raw_free ps_so set_so_ps (S f) len (os_cap st) (os_blk st)) s
        (ov_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B O len c st m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 OSS_OVERFLOW) fc None m (seg_rom psegs)).

Definition src_ok (LB0 : list block) (O B S N : Z) : Prop :=
  (exists bk, In bk LB0 /\ blk_addr bk <= S /\ S + N <= blk_addr bk + blk_size bk) \/ (O + 264 <= S /\ S + N <= B).

Definition xsputn_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (O len N : Z) (st : ossst) (m : mem)
    (ch : @chst bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (st' : ossst),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo q /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ ch = os_ch st' /\ os_w st' = os_w st + N
    /\ RHEAP s' (osblocks st' ++ LB0) m'
    /\ SBINV m' O len st'
    /\ lx_pres LB0 q [(O + 8, O + 112)] m m'.

Definition xsputn_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
         (O len S N : Z) (st : ossst) (bs : list byte),
  RHEAP s (osblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
  stk psegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - OSS_XSPUTN_STACK ->
  rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m ->
  q <= O -> O + 264 <= B -> imp_vt_rows m ->
  0 <= len <= SJ_PADMAX -> SBINV m O len st ->
  rw_cells psegs m S [CB (Z.to_nat N) bs] -> 1 <= N -> 0 <= S -> src_ok LB0 O B S N ->
  os_w st + N <= PJ_OUTMAX len ->
  implM psegs (pj_part raw_malloc raw_free ps_so set_so_ps (os_fuel st) len (os_cap st) (os_blk st)) s
        (xsputn_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B O len N st m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 OSS_XSPUTN) fc None m (seg_rom psegs)).

Definition put_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (O len N : Z) (st : ossst) (m : mem)
    (ch : @chst bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (st' : ossst),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 O) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo q /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ ch = os_ch st' /\ os_w st' = os_w st + N
    /\ RHEAP s' (osblocks st' ++ LB0) m'
    /\ OSSINV m' O len st' 0x20 /\ LOCB m'
    /\ lx_pres LB0 q [(O, O + 264)] m m'.

Definition put_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
         (O len BUF N : Z) (st : ossst) (bs : list byte),
  RHEAP s (osblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
  stk psegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - OSS_PUT_STACK ->
  rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m ->
  q <= O -> O + 264 <= B -> imp_vt_rows m ->
  rw_cells psegs m PJ_WIDEN_SLOT [C8 (Z_to_bv 64 PJ_DO_WIDEN)] -> rw_cells psegs m PJ_GOT_CTYPE_ID [C8 (Z_to_bv 64 PJ_CTYPE_ID)] -> LOCB m ->
  0 <= len <= SJ_PADMAX -> OSSINV m O len st 0xFFFFFFFF ->
  rw_cells psegs m BUF [CB (Z.to_nat N) bs] -> 0 <= N -> 0 < BUF -> src_ok LB0 O B BUF N ->
  os_w st + N <= PJ_OUTMAX len ->
  implM psegs (pj_part raw_malloc raw_free ps_so set_so_ps (os_fuel st) len (os_cap st) (os_blk st)) s
        (put_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B O len N st m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 O) (Z_to_bv 64 BUF) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 OSS_PUT) fc None m (seg_rom psegs)).

Definition oss_ctor_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo O len : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 224, q); (O, O + 264)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo q
    /\ OSSINV m' O len (oss0 O) 0xFFFFFFFF /\ LOCB m'.

Definition oss_ctor_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo O len : Z) (junk : list byte),
  stk psegs m lo q -> GLOBALS_TOP <= lo -> lo <= q - OSS_CTOR_STACK -> 0 <= q ->
  q <= O -> O + 264 < 2^62 -> rw_cells psegs m O [CB 264 junk] ->
  imp_vt_rows m -> LOCB m -> mem_inv psegs m -> 0 <= len ->
  evt psegs (oss_ctor_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo O len m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 O) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OSS_CTOR) fc None m (seg_rom psegs)).

Definition imp_S (L : Z) : Z := if Z.lor L 7 =? 23 then 26 else Z.lor L 7 + 1.

Definition str_short_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo O R L : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (bs : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 64, q); (R, R + 24); (O + 96, O + 104)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo q
    /\ rw_cells psegs m' R [C1 (Z_to_bv 8 (2 * L)); CB 23 bs]
    /\ (exists hm, rw_cells psegs m' (O + 96) [C8 (Z_to_bv 64 hm)]).

Definition str_short_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo O len R : Z) (st : ossst) (junk : list byte),
  stk psegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - 64 -> 0 <= q ->
  q <= O -> O + 264 < 2^62 -> q <= R -> R + 24 < 2^62 -> (R + 24 <= O \/ O + 264 <= R) ->
  rw_cells psegs m R [CB 24 junk] -> SBINV m O len st -> os_w st <= 22 -> mem_inv psegs m ->
  evt psegs (str_short_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo O R (os_w st) m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 R) (Z_to_bv 64 (O + 8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OSS_STR) fc None m (seg_rom psegs)).

Definition str_long_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo B O R L : Z) (m : mem)
    (b : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (NEW : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo q /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((b, NEW, imp_S L) :: LB) m'
    /\ rw_cells psegs m' R [C8 (Z_to_bv 64 (imp_S L + 1)); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 NEW)]
    /\ (exists bs, rw_cells psegs m' NEW [CB (Z.to_nat (imp_S L)) bs]) /\ rblock_range NEW (imp_S L)
    /\ (exists hm, rw_cells psegs m' (O + 96) [C8 (Z_to_bv 64 hm)])
    /\ lx_pres LB q [(R, R + 24); (O + 96, O + 104)] m m'.

Definition str_long_stmt : Prop :=
  forall (A : Type) (K : bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
         (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
         (O len R : Z) (st : ossst) (junk : list byte),
  RHEAP s (osblocks st ++ LB) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
  stk psegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - OSS_STR_STACK ->
  rw_cells psegs m LX_ERRNO [C4 errv] -> mem_inv psegs m ->
  q <= O -> O + 264 <= B -> q <= R -> R + 24 <= B -> (R + 24 <= O \/ O + 264 <= R) ->
  rw_cells psegs m R [CB 24 junk] -> 0 <= len <= SJ_PADMAX -> SBINV m O len st -> 23 <= os_w st -> os_w st <= PJ_OUTMAX len ->
  (forall b s' ms', str_long_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (osblocks st ++ LB) lo B O R (os_w st) m b s' ms' -> implM psegs (K b) s' Q ms') ->
  implM psegs (mbind (newnt lops (imp_S (os_w st))) K) s Q
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 R) (Z_to_bv 64 (O + 8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 OSS_STR) fc None m (seg_rom psegs)).

Lemma land1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. pose proof (Z.land_ones x 1 ltac:(lia)) as H. change (Z.ones 1) with 1 in H. change (2 ^ 1) with 2 in H. exact H. Qed.
Lemma long_byte0 : forall cap, cap mod 2 = 0 -> Z.land ((cap + 1) mod 256) 1 = 1.
Proof. intros cap HE. rewrite land1_mod2. Z.div_mod_to_equations. lia. Qed.
Lemma short_byte0 : forall sz, Z.land (2 * sz) 1 = 0.
Proof. intros sz. rewrite land1_mod2. Z.div_mod_to_equations. lia. Qed.
Lemma short_size : forall sz, 0 <= sz -> Z.shiftr (2 * sz) 1 = sz.
Proof. intros sz H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia. Qed.
Lemma testbit_capmask : forall n, 0 <= n -> Z.testbit 18446744073709551614 n = ((1 <=? n) && (n <? 64))%bool.
Proof.
  intros n Hn. change 18446744073709551614 with (2 * Z.ones 63).
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) at 1 by lia. rewrite Z.testbit_even_succ by lia.
    destruct (Z.lt_ge_cases (n - 1) 63).
    + rewrite Z.ones_spec_low by lia. symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
    + rewrite Z.ones_spec_high by lia. symmetry. apply Bool.andb_false_intro2. apply Z.ltb_ge. lia.
Qed.
Lemma long_capmask : forall cap, cap mod 2 = 0 -> 0 <= cap -> cap < 2^63 -> Z.land (cap + 1) 18446744073709551614 = cap.
Proof.
  intros cap HE H0 H1. set (h := cap / 2). assert (EC : cap = 2 * h) by (subst h; Z.div_mod_to_equations; lia). rewrite EC.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, testbit_capmask by lia.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    destruct (Z.lt_ge_cases (n - 1) 63).
    + replace ((1 <=? Z.succ (n - 1)) && (Z.succ (n - 1) <? 64))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia]). apply Bool.andb_true_r.
    + replace ((1 <=? Z.succ (n - 1)) && (Z.succ (n - 1) <? 64))%bool with false
        by (symmetry; apply Bool.andb_false_intro2; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
      destruct (Z.eq_dec h 0) as [->|HZ]; [rewrite Z.bits_0; reflexivity|].
      symmetry. apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 62); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_low3 : forall L, 0 <= L -> Z.lor L 7 = 8 * (L / 8) + 7.
Proof.
  intros L HL. change 7 with (Z.ones 3).
  rewrite <- (Z.lor_ldiff_and L (Z.ones 3)) at 1.
  rewrite <- Z.lor_assoc.
  assert (R : Z.lor (Z.land L (Z.ones 3)) (Z.ones 3) = Z.ones 3).
  { rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    destruct (Z.eq_dec (L mod 8) 0) as [E|NE]; [rewrite E; apply Z.lor_0_l|].
    apply Z.lor_ones_low; [Z.div_mod_to_equations; lia|]. apply Z.log2_lt_pow2; [Z.div_mod_to_equations; lia|]. change (2 ^ 3) with 8. Z.div_mod_to_equations; lia. }
  rewrite R.
  assert (D : Z.ldiff L (Z.ones 3) = 8 * (L / 8)).
  { rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. }
  assert (NC : Z.land (Z.ldiff L (Z.ones 3)) (Z.ones 3) = 0) by apply Z.land_ldiff.
  rewrite <- Z.lxor_lor by exact NC. rewrite <- Z.add_nocarry_lxor by exact NC. rewrite D. reflexivity.
Qed.
Lemma lor1_even : forall z, z mod 2 = 0 -> Z.lor z 1 = z + 1.
Proof.
  intros z HE. assert (NC : Z.land z 1 = 0) by (rewrite land1_mod2; exact HE).
  rewrite <- Z.lxor_lor by exact NC. symmetry. apply Z.add_nocarry_lxor. exact NC.
Qed.
Lemma lor7_alloc : forall a, 0 < a -> a mod 4 = 0 -> Z.lor (2 * (a - 1)) 7 + 1 = 2 * a.
Proof. intros a Ha HM. rewrite lor_low3 by lia. Z.div_mod_to_equations. lia. Qed.

Lemma imp_S_range : forall L, 23 <= L -> L + 1 <= imp_S L <= L + 8 /\ imp_S L mod 2 = 0 /\ imp_S L < L + 9.
Proof.
  intros L HL. unfold imp_S. rewrite lor_low3 by lia.
  destruct (Z.eqb_spec (8 * (L / 8) + 7) 23) as [E|NE]; Z.div_mod_to_equations; lia.
Qed.

Lemma imp_S_machine : forall L, 0 <= L -> imp_S L = (if Z.lor L 7 =? 23 then 26 else Z.lor L 7 + 1).
Proof. intros L HL. reflexivity. Qed.

Lemma imp_S_copy_ok : forall len L, 0 <= len -> 23 <= L -> L <= PJ_OUTMAX len -> copy_ok len (imp_S L) = true.
Proof.
  intros len L Hl HL HB. pose proof (imp_S_range L HL) as [R _]. unfold copy_ok, PJ_CAPMAX.
  apply andb_true_intro. split; [apply Z.ltb_lt; lia| apply Z.leb_le]. pose proof (PJ_OUTMAX_pos len Hl). lia.
Qed.

End WithCeiling0.
