(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase ADepot_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AModelFacts F_apoison F_aalloc_s F_aalloc1 F_aalloc2 F_aalloc3.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma poison_cells_frame_b : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, AIMG_LO <= A -> A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA HB. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells, AIMG_HI, AIMG_LO in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.
#[using="Type"] Lemma lt_pow2_of_log2 : forall a k, 0 <= a -> Z.log2 a < k -> a < 2 ^ k.
Proof.
  intros a k Ha Hl. destruct (Z.eq_dec a 0) as [->|]. { cbn in Hl. Local Ltac2 Set LiaHints.tbl := fun () => "0060=41415986077.44686355236.8 51794598124.451796577670.851796692231.759314873579.900000100400800;00A00GSS1GS2HlS1KS2Hl1HS2Hl1H".
apply Z.pow_pos_nonneg; lia. }
  assert (K : 0 <= k) by (pose proof (Z.log2_nonneg a); lia).
  destruct (Z.lt_ge_cases a (2 ^ k)) as [L|G]; [exact L|]. exfalso.
  assert (k <= Z.log2 a). { rewrite <- (Z.log2_pow2 k) by lia. apply Z.log2_le_mono. lia. } lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma hdr_b1_mid_range : forall b1, 0 <= b1 -> 0 <= hdr_b1_mid b1 < 256.
Proof.
  intros b1 Hb. unfold hdr_b1_mid.
  set (x := Z.lor (Z.land b1 18446744073709551612) 1).
  Local Ltac2 Set LiaHints.tbl := fun () => "0080=21729222224.650071946878.750653792827.362997561758.662997709214.565502300846.66755913196.3 68106533001.600000400800<00=00>00?00@00DS2A0S2L1S2HbSSSSS2A0".
assert (X0 : 0 <= x) by (subst x; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; lia| lia]).
  assert (A0 : 0 <= Z.land x 143) by (apply Z.land_nonneg; right; lia).
  split. { apply Z.lor_nonneg. lia. }
  change 256 with (2^8). apply lt_pow2_of_log2. { apply Z.lor_nonneg; lia. }
  rewrite Z.log2_lor by lia.
  pose proof (Z.log2_land x 143 X0 ltac:(lia)) as L1.
  replace (Z.log2 143) with 7 in L1 by reflexivity. replace (Z.log2 16) with 4 by reflexivity. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
End CANSEC1.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Notation allocate_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 1152, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocate_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (allocate_W L sp t c AB UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells asegs m' (t + 2784) [C8 stj']
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat n))]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

#[using="Type"] Lemma allocate_fast_spec : forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (n S t c cnt spacebeg AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (maxc csz stj idxw j1 j2 : word) (pj : byte)
    (chunks sj : list word) (sjunk uj : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 1152 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= 448 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0x9e6cd [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0x9e6a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0x99a90 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m 0x5d3e20 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x132940 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x9d838 [C8 (Z_to_bv 64 spacebeg)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  Z.shiftr (needed_size n + 31) 5 = c ->
  rw_cells asegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 208 + c * 80 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  0 <= spacebeg < 2^47 ->
  (* [comment removed for export] *)
  AB = spacebeg + c * 2^32 + 16 * bv_unsigned idxw ->
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 56 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF asegs RNG (allocate_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros until tr. cbv zeta.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 N AC PC PP FLG LS1 LS2 HK SB CT8 TT0 STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CR CH LCH CNT NTH IXS STS SBR HAB HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 SS SZ SZB TB LTB TRF TRU SPS S47 DEP
         RIMG RSTK RS RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.   (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "00g0?11752483811.16611910114451.23613455802737.24415401259710.20717058309717.2081744903108.208 17949008832.26919323711443.2361935690314.184 2250029779.242 24786325331.23626496924968.20826496924968.20928573890679.14 28774064144.20829311285958.17429542474835.23630242941139.24235211722144.2083573724046.212 37040831591.20837386977061.24238921699923.23644073400224.2084686064224.208 46988300803.16647432010528.20850655895377.24152569147371.23652569147371.24052569147371.24652569147371.26852640706144.2085449560974.209 54768058737.24654969794426.24256515121377.21156956174629.20857818248480.20860050799059.23661871085715.23662588846521.20863136544723.24263616979104.20864300782718.18464675990227.23664897170030.24265450282016.20867100501013.2  67469470029.21567469470029.55 7048756266.208 8806422860.14  9025712081.184 9025712081.185 00000500g02G02N02f03:04R05D05L06>07007H09;09?0:00:50:g0;Y0<J0=R0>40><0>n0?_0@P0@U0AF0AN0B@0DD0FN0HE0I60JM0Kg0L00M00M80Mi0N[0OM0O]0PO0Q@0QW0RI0R^0SO0ST0T_0Ue0V40V>0V?0VOS3LCHS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS4CEIL2LO1N3LSJ2T03LCH3HUB4ABLO4UBHI4AB163NSZ3HPG3SB42N12R13LTB4PW012NS3RZR3RZE3RSR3RSM3NSR1Y2Y0S1N3LCHS4CEIL2LO2T13LCH3SPS3C16S4CEIL2LO2T13LCH3C16S4CEIL2LO1N3LSJ2T03LCH3HUB4ABLO3HPG3SB13SB23SB33SB43LTB2NS3RZR3RSR3RSM3NSR4LSJd2NE3TS01HS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS2LO3LCHS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS4CEIL2LO2T13LCH3SPS3C16S4CEIL2LO1N3LSJ2T02T13TAL2HC3LCH3HUB4ABLO4UBHI4AB163NSZ3LTB2NS3RZR3RZE3RSR3C162DX1H3HPG3SB13SB23SB33SB43TS03CX03CX1S2HqS4CEIL2LO1N3LSJ3TAL2HC3LCH4ABLO3LTB3RSR3RSM3C161HS3LCHS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS4CEIL2LO1N3LSJ3TAL2HC3LCH4ABLO3LTB3RSR3RSM3C161HS4CEIL2LO1N3LSJ2T02T13TAL2HC3LCH3HUB4ABLO4UBHI4AB163NSZ3LTB3NSR3C162DX1HS1N3LSJ2T03TAL2HC3LCH4ABLO3LTB3C16S2LO3LCHS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS4CEIL2LO1N3LSJ3TAL2HC3LCH4ABLO3LTB3RSR3RSM3C161HS4CEIL2LO1N3LSJ3TAL2HC3LCH4ABLO3LTB3RSR3RSM3C161HS3LCHS4CEIL2LO1N3LSJ3TAL2HC3LCH4ABLO3LTB3RSR3RSM3C161HS3LCH2B1S4CEIL2LO3LCH4UBHI3NSZ3HPG3SB42N12R14PW012NS3RSR1HS4CEIL2LO1N3LSJ2T02T13TAL3LCH3HUB4ABLO4AB163HPG3SB13SB23SB33SB42N12R13LTB2NI2SI4PW013RZR3RZE1Y2Y02Y13TS01H3CX03CX14UBHI3NSZ3NSR4CXS0S4CEIL2LO1N3LSJ2T02T13TAL2HC3LCH3IXS3SBR3HAB3HUB4ABLO4UBHI4AB163NSZ3HPG3SB13SB23SB33SB42N12R13LTB2NI2SI4PW013RZR3RZE3NSR3C161Y2Y02Y13TS01HS4CEIL2LO1N3LSJ2T02T13TAL2HC3LCH3HUB4ABLO4UBHI4AB163NSZ3LTB2NS3RZR3RZE3RSR3NSR3C164LSJd1Y1H3HPG3SB13SB23SB33SB43RSM3TS0S4CEIL2LO1N3LSJ3TAL2HC3LCH4ABLO3LTB3RSR3RSM3C161HS4CEIL2LO1N3LSJ2T02T13TAL2HC3LCH3HUB4ABLO4UBHI4AB163NSZ3LTB2NS3RZR3RZE3RSR3NSR3C162DX1HS4CEIL2LO1N3LSJ2T03LCH3HUB4ABLO4UBHI3NSZ3HPG3SB42N12R13LTB4PW012NS3RZE3RSR3RSM2RZ3RZC1Y2Y0S3CX03LCHS4CEIL2LO1N3LSJ2T03LCH4ABLO3HPG3SB13SB23SB33SB43LTB3C162NE3TS01HS2LO3LCHS4CEIL2LO1N3LSJ3TAL2HC3LCH4ABLO3LTB3RSR3RSM3C161HS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS3LSJ2T03LCH3LTBS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS4CEIL2LO1N3LSJ3TAL2HC3LCH4ABLO3LTB3RSR3RSM3C161HS4CEIL2LO3LCH3SPS3S471HS4CEIL2LO3LCH3HUB4ABLO3HPG3SB13SB23SB32NI2SI3RZR1HS3LCH4UBHI3NSZ2NS3RSRS4CEIL2LO1N3LSJ3TAL2HC3LCH4ABLO3LTB3RSR3RSM3C161HS3NSRS4CEIL2LO3LCH2N12R12Ha1H1N3LSJ2T03IXS3SBR3HAB4ABLO4AB163LTB2NI2SI3C162X12X2S4CEIL2LO2N12R12Ha1H1N3LSJ2T04ABLO2NI2SI1Y2Y02Y12Y23HUB2NS3RZR3RSR3NSRS4CEIL2LO3LCH1HS1N3C162HqFS3LSJ3LCH3LTB2DX".
assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; clear -NSR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).   (* [comment removed for export] *)
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m n S (al_ctx L) t c cnt spacebeg lo maxc csz stj chunks idxw);
      try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fastR; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (with_box CT2 lia). all: try solve_rng. }
  cbv beta. intros ms1 PA. unfold allocA_post in PA. destruct_exs PA.
  destruct PA as (-> & MUa & WMa & MIa & STa & [fr0 FRa] & CRa & [stja STSa]).
  rewrite <- HAB.
  (* [comment removed for export] *)
  xport HDR MUa WMa ltac:(with_box DJT lia). xport SHA MUa WMa ltac:(with_band TS lia). xport SHU MUa WMa ltac:(with_band TS lia).   (* [comment removed for export] *)
  xport PP MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(with_box CT2 lia). xport TT0 MUa WMa ltac:(lia).
  xport SS MUa WMa ltac:(lia). xport TB MUa WMa ltac:(rewrite LTB; lia).
  xport STATS MUa WMa ltac:(rewrite LSJ; lia). xport CT MUa WMa ltac:(with_box CT2 lia).
  xport UJ MUa WMa ltac:(with_box DJT lia).
  xport FLG MUa WMa ltac:(lia). xport LS1 MUa WMa ltac:(lia). xport LS2 MUa WMa ltac:(lia). xport HK MUa WMa ltac:(lia).
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  assert (PC1 : poison_cells x13).
  { eapply poison_cells_frame_b; [exact PC | exact MUa | exact WMa |]. unfold AIMG_HI, AIMG_LO.   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs x13 PG [C1 pj]).
  { intros NE. specialize (SHP NE). xport SHP MUa WMa ltac:(with_band TS lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells asegs x13 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). xport LH MUa WMa ltac:(with_box DJT lia). exact LH. }
  assert (DEP1 : ADEPOT DI L x13).
  { eapply (adi_frame DI); [exact DEP | exact MUa | exact WMa |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; pose proof DTN as X1; unbox X1; pose proof DTS as X2; unbox X2; lia|]).
    apply Forall_nil. }
  clear SHP LH PC DEP.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (allocBC_spec DI L RNG sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc x13 n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STa
         | |- mem_inv _ _ => exact MIa
         | |- poison_cells _ => exact PC1
         | |- ADEPOT _ _ _ => exact DEP1
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP1
         | |- _ -> rw_cells _ _ _ _ => exact LH1
         end.
    all: try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fastR. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_post in PB. destruct_exs PB.
  destruct PB as (-> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).
  (* [comment removed for export] *)
  xport FRa MUb WMb ltac:(lia).
  xport STATS MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia).   (* [comment removed for export] *)
  xport TI MUb WMb ltac:(lia). xport TK MUb WMb ltac:(lia). xport T88 MUb WMb ltac:(lia). xport TSD MUb WMb ltac:(lia).
  xport CT MUb WMb ltac:(ub DJC; ub DCN; ub DCS; with_band CXS lia).
  xport FLG MUb WMb ltac:(lia). xport LS1 MUb WMb ltac:(lia). xport LS2 MUb WMb ltac:(lia). xport HK MUb WMb ltac:(lia).
  destruct PC1 as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(lia). xport GOT80 MUb WMb ltac:(lia). xport REAL MUb WMb ltac:(lia).
  xport UJ MUb WMb ltac:(ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia). xport STSa MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs x32 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH1 RZ). pose proof (rz_size_small_cases n N) as RZC.
    xport LH1 MUb WMb ltac:(ub DJN; ub DJS; lia). exact LH1. }
  clear LH1 SHP1.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (allocD_spec L RNG sp gp tp F fc x32 n t c AB UB lo b0 (hdr_b1_mid b1) x14 S sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fastR. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_post in PD. destruct_exs PD.
  destruct PD as (-> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  xport CRa MUd WMd ltac:(ub DJT; lia). xport STSa MUd WMd ltac:(ub DJT; lia).
  xport SHUb MUd WMd ltac:(with_band TS lia).   (* [comment removed for export] *)
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs x47 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(with_band TS lia). exact SHPb. }
  assert (DEPd : ADEPOT DI L x47).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha SPR S47 CEIL LO T0 T1 TAL NI SI N0 N1 R0 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (MU : munch (allocate_W L sp t c AB UB PG pgw n) m x47).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUb]].
    eapply munch_weaken; [| exact MUa].
    all: first [clear -N C16 PW01; unfold sub_fp; cbn [outside]; intros q Hq; lia | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }   (* [comment removed for export] *)
  assert (WM : wmono asegs m x47).
  { eapply wmono_trans; [| exact WMd]. eapply wmono_trans; [exact WMa | exact WMb]. }
  unfold allocate_post. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LHd|]. split; [exact SHUb|]. split; [exact SHPd|]. exact DEPd.
  Unshelve. all: try exact STb.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithDepot.
End CANSEC2.
(* [comment removed for export] *)
