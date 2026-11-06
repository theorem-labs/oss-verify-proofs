(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AKitQ F_apoison F_aenqueue F_aenqueueR F_adrain F_aput F_afree_tail.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. Local Ltac2 Set LiaHints.tbl := fun () => "0020>56459188277.9 56461269045.1400000400=S2HES2H12H21H".
destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.  (* [comment removed for export] *)

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6250496 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. Local Ltac2 Set LiaHints.tbl := fun () => "0020=24437255187.543957821123.500000900?S1H2H02G2S1H2H0".
destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6250496 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition put_to_refill_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo lst nx bsz : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x35630) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2
                  (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0x9d818) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35e10) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -144)
    /\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -144)
         [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0x9daf0); C8 (Z_to_bv 64 0x354d0)]
    /\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True).

#[using="Type"] Lemma put_to_refill_spec : forall (full : bool) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz : Z) (maxc csz : word) (hs : list word) (sjunk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0x9daf0 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x9db30 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0x98e30 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0x9e6a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_to_refill_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t hm n lo lst nx bsz hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3532c) fc None m (seg_rom asegs)).
Proof.
  intros until sjunk. intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO HHI HCE SH QC NB LST T0 T1 TAL DHT FULL CR DTL DHL RIMG RSTK RT RH RSH TI.
  Local Ltac2 Set LiaHints.tbl := fun () => "0220?10511405345.12510511405345.13011801586693.12811801586693.13311801586693.15611801586693.16111807744665.15111807744665.15612239306608.1  12502592091.10213313577562.3  13714634046.14813714634046.15314259101031.15315795316387.14815795316387.15316948956174.14217554424355.14817554424355.1531770151705.126 1770151705.131 18954152602.1421937063194.137 1937063194.142 19838492861.12819838492861.13320010950973.12820010950973.13320010950973.15620010950973.16122165772157.12822165772157.13322165772157.15622165772157.16122280066330.13722280066330.14222290347171.14822290347171.15324436996044.3  25076071819.14825076071819.15326010845258.11326010845258.11826060559118.12826060559118.13326060559118.13926060559118.14426387766345.4  26892418956.1  27506090268.4  29782367974.10129782367974.10330665193763.14830665193763.15331558035817.10134659058725.12634659058725.13134659058725.13734659058725.14235397829149.10035895327997.12835895327997.13337023859802.1  37829417582.12737829417582.13237838061989.13837838061989.14338903098019.14838903098019.15340163316356.1  41480320778.97 43358680699.82 43358680699.98 43887101897.5  44392278835.11344392278835.11846752305619.12646752305619.13147419153970.12647419153970.13148199399523.14848199399523.15349610168957.12849610168957.13349776114715.12649776114715.13149821043939.14849821043939.15352916306408.3  54070930666.13754070930666.14255083526051.14855083526051.15355468805949.15655475224993.13356170256219.12856170256219.13356170256219.13956170256219.14456323790752.12856323790752.13356330475836.15156330475836.15657441639435.3  58477402019.14858477402019.15359711299560.2  60722501712.5  6076365731.148 6076365731.153 63632204029.12863632204029.1336389036148.142 64548988925.12864548988925.13364548988925.15664548988925.16165128844401.12665128844401.13165188488701.12865188488701.1337225802193.149 7225802193.154 7848643581.128 7848643581.133 8838673686.146 8838673686.151 8949264304.3   9405451517.128 9405451517.133 00000400=00Q00m01=01M01`02602702P02Q03:03c04:04K04\04`05105B05G05L05P05T05X05a05j06306<06I06V06_06h07507B07F07J07[07l08108O09809<09@09O09^09m0:<0:=0:>0:?0:@0:A0:R0:c0;60;:0;>0;B0;F0<10<:0<C0<D0<E0<F0<P0<`0=10=B0=C0=I0=O0=U0=V0=Y0=\0=]0=^0=c0=h0>90>J0>S0>\0>c0>j0?;0?L0?Q0?V0?[0?l0@=0@I0@U0@Z0@_0@d0@i0A>0AS0Ah0B=0BB0BS0Bd0Be0Bf0C70CH0CQ0CZ0C_0Ch0D10D>0DK0DL0DM0DV0D_0D`0Da0Dj0E30E40E50E:0EC0ELS2ALS2AL4LEN0S4CEIL2LO2T13SHB3SHLS4CEIL2LO2T13SHB3SHL2L14LEN0S4CEIL2LO2T13HspS4CEIL2LO2T13HspS4CEIL2LO3SHB3SHL1HS4CEIL2LO3SHB3SHL1H2L1SS1N3DHT3DTL3DHL5KBHLO3RUPFS4CEIL2LO1N5KEHLO5KCHLO5KDHLO3SHB3RUP3HspS4CEIL2LO1N5KEHLO5KCHLO5KDHLO3SHB3RUP3HspS4CEIL2LO2L02L13SHB3HspS4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspS2L0S4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspS3HL4S3HL4S2L1S2T1S2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS2NBS2NBS4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspS3HspS4CEIL2LO3SHB3Hsp2T14KBT04KCT0S4CEIL2LO3SHB3Hsp2T14KBT04KCT02L02L14LEN0S2LOS2LOS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HFSSSSS4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspS3DHT3DTL3DHL5KBHLOS2LOS2LOS2LOS2LOS2AL3DHT3DTL3DHL2TI5KBHLO5KEHLO5KCHLO5KDHLOS4CEIL2LOS4CEIL2LOFFFS3LST4LST0S3LST4LEN03HL21YS4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspSS4KBTIS2T11HS2T11HFS1NS1NSSS3RUPS3RUPS4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspS4CEIL2LOS4CEIL2LOS1N3RUPS1N3RUPS4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspS3HspS3LSTS3LSTS4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspS4CEIL2LO2L1S4CEIL2LO2L1S3HspS3HspS3HspS3HspS4CEIL2LO1N5KDHLO3RUPS4CEIL2LO1N5KDHLO3RUPS4CEIL2LO1N5KDHLO3RUPS4CEIL2LO1N5KDHLO3RUPS3HspS4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspSSS4CEIL2LO3SHB3HspS4CEIL2LO3SHB3HspS4CEIL2LOS4CEIL2LOS3NB1S4CEIL2LOS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspSSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOSSS3HspS4CEIL2LOS4CEIL2LO".
band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148232192 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  box DHT. box DTL. box DHL.
  destruct full; [destruct FULL as (NB1 & LB & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]];
  unfold AIMG_HI in *.
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box SH'. box LA0. box LB. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec true t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | split; [lia|]; split; [ub LB; exact Y|]; split; [unfold AIMG_HI; lia|]; split; [unfold Q_BATCH_BYTES; lia| exact RL]
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; lia). carry LB MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. all: try exact I. all: try (split; assumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells asegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.
    step.
    box HD. box SH'. box FRP.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80)]%Z MUe WMe.
    box ST.
    call_sp (enqueue_to_refill_spec false t lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo maxc csz);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact QC| lia| lia
      | exact NB0
      | exact CR| exact TI| atop_facts; lia| exact TAL| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in * by lia.
    unfold put_to_refill_post. finish.
    all: try assumption. all: try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. all: try exact I.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma put_from_refill_spec : forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk asegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv asegs m ->
  a2 = Z_to_bv 64 (t + 208) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0x9daf0); C8 (Z_to_bv 64 0x354d0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x9db30 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells asegs m 0x9d838 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  (* [comment removed for export] *)
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF asegs RNG (put_tail_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35630) fc None m (seg_rom asegs)).
Proof.
  intros until j0. cbv zeta. intros ST CEIL LO MI -> FRP FRE QK HD N AL HLO HHI HCE SH' QC NB QB QBN FST LST T0 T1 TAL DHT
    FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB DK RIMG RSTK RT RH RSH TI.
  Local Ltac2 Set LiaHints.tbl := fun () => "0860?10407789017.15110407789017.15510407789017.15810407789017.16210407789017.16910645443711.20510651740231.20010725364317.15010725364317.15410725364317.15710725364317.16110725364317.16810952616835.4  1107224959.170 1107224959.174 1107224959.176 1107224959.180 1107224959.181 1107224959.187 11102352194.4  11148197578.3  11472836995.17611472836995.18211472836995.19611472836995.20111472836995.20211472836995.2071162083361.182 1162083361.188 1162083361.189 1162083361.195 11946474072.4  12502592091.13312510265625.4  12922960306.2  13082525187.4  13439304920.4  14442771078.17614442771078.18214442771078.18314442771078.18914628713459.17614628713459.18214628713459.18314628713459.18914855542522.4  15328766942.15015328766942.15415328766942.15715328766942.16115328766942.16815763621304.4  1634912969.5   16494042243.4  16948956174.15716948956174.16116948956174.16816955067115.19816955067115.20416955067115.20516955067115.21116957164239.17216957164239.17616957164239.17916957164239.18316957164239.1901727484261.151 1727484261.155 1727484261.158 1727484261.162 1727484261.169 1761686644.150 1761686644.154 1761686644.157 1761686644.161 1761686644.168 17720676986.4  17768188966.15717768188966.16117768188966.16817776320428.19517776320428.20017776320428.20117776320428.20617776320431.17617776320431.18217893525560.4  17930314345.15217930314345.15617930314345.15917930314345.16317930314345.170182225607.4    1937063194.150 1937063194.154 1937063194.157 1937063194.161 1937063194.168 1937063194.176 1937063194.182 1937063194.183 1937063194.189 19710306796.18319710306796.18419710306796.18919710306796.19019837149718.17619837149718.18019837149718.18319837149718.18719837149718.19422226183811.17722226183811.18322226183811.19722226183811.20222226183811.20322226183811.20822280066330.15022280066330.15422280066330.15722280066330.16122280066330.16822946482422.5  23117118514.5  23256998737.4  23955338831.17223955338831.17623955338831.17923955338831.18323955338831.1902417594528.4   2431248216.150 2431248216.154 2431248216.157 2431248216.161 2431248216.168 24383500448.18924383500448.19424383500448.19524383500448.20024389384212.16924389384212.17524436996044.3  24486622407.5  24551115864.4  2465323422.4   24686499148.5  24798753991.5  25355755472.3  25878270255.17625878270255.18225878270255.19625878270255.20125878270255.20225878270255.20725928844135.5  26045504544.4  26060559118.17826060559118.18426060559118.18526060559118.19127285807279.15227285807279.15627285807279.15927285807279.16327285807279.17027625238687.5  27710955247.4  27723960707.17627723960707.18227723960707.19627723960707.20127723960707.20227723960707.20727726171459.5  28373285208.4  28501102824.4  28657317337.17628657317337.18228657317337.18328657317337.18928686419730.17228686419730.17628686419730.17828686419730.18228686419730.18328686419730.18928686419730.19328686419730.19928686419730.20528868026202.3  2887535744.4   29782367974.13229782367974.13430047027402.3  30391224920.4  30396517883.3  3051486595.177 3051486595.183 3051486595.196 3051486595.201 3051486595.202 3051486595.207 31474781846.16931474781846.17331474781846.17531474781846.17931474781846.18031474781846.18631558035817.1323216195529.5   33572432657.4  34007733848.4  34280497042.16934280497042.17334280497042.17534280497042.17934280497042.18034280497042.18634289656700.5  34594790036.4  34758801994.3  35223967026.19935223967026.20535223967026.20635223967026.21235397829149.13135796352011.15035796352011.15435796352011.15735796352011.16135796352011.16836115622447.17636115622447.18236115622447.19636115622447.20136115622447.20236115622447.20737437981368.15037437981368.15437437981368.15737437981368.16137437981368.16837838061989.15137838061989.15537838061989.15837838061989.16237838061989.16938239729458.3  38823039235.4  39066829767.5  40044305373.15740044305373.16140044305373.16840091925679.18040091925679.18640091925679.18740091925679.19340366242410.4  413869744.3    41387447901.15241387447901.15641387447901.15941387447901.16341387447901.17041480320778.12841993533502.17641993533502.18241993533502.18341993533502.18942200251523.17742200251523.18342200251523.19742200251523.20242200251523.20342200251523.20842634571787.3  42826209617.4  4325339749.150 4325339749.154 4325339749.157 4325339749.161 4325339749.168 43358680699.11343358680699.12943987951406.17743987951406.18343987951406.19743987951406.20243987951406.20343987951406.20844832095178.15044832095178.15444832095178.15744832095178.16144832095178.16844832095178.18244832095178.18944851608341.4  44934367832.4  44947310317.18344947310317.18944954880536.15044954880536.15444954880536.15744954880536.16144954880536.16845437524262.17645437524262.18245437524262.18345437524262.18946296523843.5  4684977269.152 4684977269.156 4684977269.159 4684977269.163 4684977269.170 46887021955.17746887021955.18346887021955.19746887021955.20246887021955.20346887021955.20847557153310.4  476510808.4    47867967832.4  47899892029.18347899892029.18947944276846.4  48415358463.15748415358463.16148415358463.1684913304334.152 4913304334.156 4913304334.159 4913304334.163 4913304334.170 49870597903.18149870597903.18749870597903.18849870597903.19449871227480.4  50001098077.4  50135352337.4  50628941955.18350628941955.18950628941955.19050628941955.19650914456032.4  50915327826.17650915327826.18050915327826.18250915327826.18650915327826.18750915327826.19351622485008.3  51678667180.17551678667180.18151678667180.19551678667180.20051678667180.20151678667180.20652567063507.19352567063507.19452567063507.19952567063507.20052569147371.16952569147371.17152569147371.17352569147371.17552569147371.17752569147371.17952569147371.18052569147371.18152569147371.18252569147371.18352569147371.18652569147371.18852569147371.18952569147371.19852569147371.19952569147371.20452569147371.20552577405267.19852577405267.20452577405267.20552577405267.21152579502455.17252579502455.17652579502455.17952579502455.18352579502455.19052916306408.3  53133017033.5  53767577775.17653767577775.18253767577775.19653767577775.20153767577775.20253767577775.20753972425513.19453972425513.20053978720017.19953978720017.20554070930666.15054070930666.15454070930666.15754070930666.16154070930666.1685463296246.5   54879733238.5  55405207249.4  56161161617.4  56170256219.17856170256219.18456170256219.18556170256219.19157063869568.4  57708434993.4  58907684060.17658907684060.18258907684060.18358907684060.18958938013242.17658938013242.18258938013242.18358938013242.1895896867971.176 5896867971.182 5896867971.197 5896867971.202 5896867971.203 5896867971.208 59067160960.4  59267440287.3  59314873579.17059314873579.17459314873579.17659314873579.18059314873579.18159314873579.18759506921496.16859506921496.17459506921496.18859506921496.19359506921496.19459506921496.19959536183085.17759536183085.18159536183085.18359536183085.18759536183085.18859536183085.19460305114944.15060305114944.15460305114944.15760305114944.16160305114944.16860630562193.4  60837831747.5  61355779793.5  61542989279.3  61602386179.4  61850333874.3  61917199020.17561917199020.18161917199020.19561917199020.20061917199020.20161917199020.20661994440323.17861994440323.18461994440323.19861994440323.20361994440323.20461994440323.20962450687107.4  63235321900.17563235321900.18163235321903.19663235321903.20163235321903.20263235321903.20763816947407.4  6389036148.157 6389036148.161 6389036148.168 64864250862.15064864250862.15464864250862.15764864250862.16164864250862.16864951437881.4  67260705573.17667260705573.18267260705573.18367260705573.1896785386107.3   68459972047.17268459972047.17668459972047.17968459972047.18368459972047.1907217643664.3   770174668.157  770174668.161  770174668.168  8419811407.172 8419811407.176 8419811407.179 8419811407.183 8419811407.190 8421908587.198 8421908587.204 8421908587.205 8421908587.211 8446433082.4   9279663253.4   00000=00J00Z01201B01n02W02`02i03203;03D03E03J03O03T03Y03^03c03d03e03j03o04004504604;04C04K04S04[04\05H05I05M05N05O05^05m06<06K06S06[06c06k06l07;07J07Y07h08708808908:08B08J08R09309T0:20:P0:g0;>0;S0;m0<B0<M0<X0<h0=80=H0=P0=X0=`0=h0>00>10>90>A0>I0>Q0>Y0>a0>i0?10?90?:0?;0?<0?=0?>0??0?@0?H0?P0?X0?`0?h0@00@80@@0@H0@I0@T0@U0@e0@f0@g0@h0@i0@j0@o0A40A50A:0A;0A@0AH0AP0AX0A`0Ah0Ai0Aj0Ak0BB0BY0Bn0CH0C]0C^0Ce0Cl0D30D:0DA0DI0DQ0DY0Da0Di0E10E60E70E80E90E:0E;0E<0ED0EL0ET0E\0Ed0El0Em0En0F=0FL0F[0Fj0G60GB0GN0GZ0Gf0Gg0Gh0Gm0H20H30H80H90H>0H?0H@0HA0HJ0HS0H_0Hk0I<0IM0Ic0J90JJ0J`0K^0Lg0Ma0Mb0Mc0Mh0Mm0Mn0Mo0N00N50N:0N;0N@0NA0NF0NG0NH0NI0NJ0NK0NL0O20O30O40O50OC0OQ0O_0Om0P;0PI0PJ0PK0PL0PM0PN0PO0PP0QJ0QS0Q\0Qe0Qn0R70R?0RG0RO0RW0R_0Rg0Ro0S70S?0SG0SO0S]0Sk0T?0TX0Tl0Tm0Tn0To0U70U?0UG0UO0UW0U_0Ug0Uh0Um0Un0Uo0V00V10V20V<0VD0VL0VT0V\0Va0Vf0Vg0Vl0Vm0W20W70W80WA0WJ0WS0W\0We0Wo0X90XA0XI0XQ0XY0Xa0Xi0Y20Y;0YD0YM0YV0Y_0Yh0Yi0Yj0Z20Z:0ZB0ZJ0ZR0ZZ0Zb0Zk0[40[=0[F0[G0[H0[I0[J0[K0[L0[Q0[V0[W0[\0[]0[b0[c0[d0[e0[m0\50\60\?0\H0\Q0\`0\o0]>0]M0]\0]a0]f0]k0^00^10^20^30^80^=0^B0^G0^H0^M0^R0^W0^\0^a0^f0^g0^o0_70_?0_G0_O0_W0`80`]0a>0an0b^0c;0ck0do0eE0f40fd0g:0gW0gh0hW0hm0iC0ia0jR0k50l10ll0mg0nS0o?0oX10110H10d11;11@11A11I11Q11Y11a11i12112V13@13h14U14^14g15015915B15C15D15E15F15O15X15a15j15k15l16616@16J16T16b17017>17L17Q17V17W17\17]17b17c17d18?18Z19:19Z1:51:U1:Z1:_1:`1:e1:f1:k1;01;51;:1;?1;D1;I1;R1;[1;d1;m1<61<71<81<91<:1<;1<<1<D1<L1<T1<\1<d1<l1=11=61=71=<1==1=B1=C1=K1=S1=[1=c1=k1>31>41>=1>F1>O1>W1>_1>g1>o1?71?81?@1?H1?P1?X1?Y1@01@G1@\1A61AK1AL1AU1A^1Ag1B>1BU1Bj1CD1CY1D:1D[1E91EW1EX1EYS4LST03LCH2B0S4LST03LCH2B0S4LEN03LCH3HL21YS4LEN03LCH3HL21Y4LST02B0S4LEN03LCH3HL21YS4CEIL2LO2T12L02L14LEN03LCH2G42TI3HL21Y2Y01HS4CEIL2LO2T12L02L14LEN03LCH2TI3HL21Y1H2H0S3QBN3LCHS3QBN3LCHS3QBN3LCHS3QBN3LCHS3QBN3LCHFS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHSSS3LCHS3LCHSS3LCHSS3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHSS1N3DHT3LCH2B03DTB3DTL3DBL3DHB3DHL5KBHLO3RUPFS2L0FSS3LCH4GFST4GLSTS3LCH4GFST4GLSTS3LCH4GFST4GLSTS3LCH4GFST4GLSTS3LCH2GQS3LCH2GQS3LCH2GQS3LCH2GQSS3HCE3LCH3HL11HS3HCE3LCH3HL11HS3HCE3LCH3HL11HS3HCE3LCH3HL11HS3HCE3LCH3HL11HFFFS2L03LCHS2L03LCHS2L03LCHS4CEIL2LO3LCH5GLST04KCTI4KDTI3HspS4CEIL2LO3LCH5GLST04KCTI4KDTI3HspS4CEIL2LO3LCH2G34KCTI4KDTI3HspS4CEIL2LO3LCH2G34KCTI4KDTI3HspS4LST03LCH2B04KCTI4KDTIS4LST03LCH2B04KCTI4KDTIS2L03LCH2B04KCTI4KDTIS2L03LCH2B04KCTI4KDTI4LST0S2L03LCH2B04KCTI4KDTIS3LCH3HL21YS3LCH3HL21YS4LEN03LCH3HL21YS4LEN03LCH3HL21YS4LEN03LCH3HL21YS2QB3LCHS2QB3LCHS2QB3LCHS2QB3LCHS2QB3LCHSS2NX3LCHS2NX3LCHS2NX3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHFFFFFFFS2T13LCHS2T13LCHS2T13LCHS2T13LCHS2T13LCHS2T13LCHS2T13LCHS2T13LCHS2T13LCHFS3LCH3HL21YFS4LEN03LCH3HL21YSSSSSS3LCHS3LCHSS3LCHSS3LCHS2NB3LCHS2NB3LCHS2NB3LCHS2NB3LCHS2NB3LCHFFFS4LST03LCH2B04KCTI4KDTIS4LST03LCH2B04KCTI4KDTIS2L03LCH2B04KCTI4KDTIS2L03LCH2B04KCTI4KDTI4LST0S2L03LCH2B04KCTI4KDTIFS1N3LCHS1N3LCHS1N3LCHS1N3LCHS1N3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3HspFFFFFFS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHFFS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2LO3LCH3HspS2LO3LCH3HspS2LO3LCH3HspS2LO3LCH3HspS2LO3LCH3HspFFS3LCHS3LCHSS3LCHSS3LCHFSSS3LCH3GQBS3LCH3GQBS3LCH3GQB2G1S3LCH3GQB2G1S3LCH3HL21Y2Y02Y1S3LCH3HL21Y2Y02Y1S4LEN03LCH3HL21Y2Y02Y1S4LEN03LCH3HL21Y2Y02Y1S3LCH3HL21Y2Y02Y1S4LEN03LCH3HL21Y2Y02Y1S4CEIL2LO1N2AL3HCE2T13LCH5GLST02TI3HL13HL25KBHLO5KDHLO3RUP1Y1HS4CEIL2LO1N2AL3HCE2T14LEN03LCH5GLST02TI3HL13HL25KBHLO5KDHLO3RUP1Y1H2G42Y0S4CEIL2LO1N3HCE2T14LEN03LCH2G42TI3HL13HL25KDHLO3RUP1Y2Y01HFFS3LCHS3LCHSSFS3LCHS3LCHSS3LCHSS3LCHFFFFFFS3DHT3LCH2B03DTB3DTL3DBL3DHB3DHL5KBHLOFFSS1N2QB3QBN3LCHS1N2QB3QBN3LCHS1N2QB3QBN3LCHS1N2QB3QBN3LCHS1N2QB3QBN3LCHS1N2QB3QBN3LCHFSSSSSSS2AL3DHT3LCH2B03DTB3DTL3DBL3DHL2TI5KBHLO5KEHLO5KCHLO5KDHLOS3LCH3SBPS3LCH3SBPS3LCH3SBPS3LCH3SBPS3LCH3SBPS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3LCH2B0S3LCH2B0S3LCH2B0S3LCH2B0S3LCH2B0S3LST4LST03LCHS3LST4LST03LCHS3LST4LEN03LCH3HL21YS3LST4LEN03LCH3HL21Y4LST0S3LST4LEN03LCH3HL21YFFFS2NX3LCHS2NX3LCHS2NX3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHSS3HspFFFFFS3LCH4KBTIS2NB3LCHS2NB3LCHS2NB3LCHS2NB3LCHS3LCHS3LCHSS3LCHSS3LCHS3HspFS3LCH3SPRS3LCH3SPRS3LCH3SPRS3LCH3SPRS3LCH3SPRS2T13LCH1HS2T13LCH1HS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3FST3LCHS3FST3LCHS3FST3LCHS3FST3LCHS3FST3LCHS3FST3LCHS3FST3LCHFSS3LCH2G3S3LCH2G3S2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3LCH3GNBS3LCH3GNBS3LCH3GNBS3LCH3GNBFFFFFFS3LCHS3LCHSS3LCHSS3LCHFSSS3LCH2G4S3LCH2G4FS3BSZ3LCHS3BSZ3LCHS3BSZ3LCHS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS3LCHS3LCHS3LCHS3LCHSFFS3LCHS3LCHS3LCHS3LCHSS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHSS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS4CEIL2LO2T13LCH4KBTI4KCTI4KDTI1HS4CEIL2LO2T13LCH2B03BL12TI3HL21Y1H2H0S4CEIL2LO2T13LCH4KBTI4KCTI4KDTI1HS4CEIL2LO2T14LEN03LCH2B03BL12TI3HL21Y1H2H02L02L1S4LST03LCH2B04KBT04KCT03SHB3SHL4CEIL2LO2T13BL11HS3TAL3LCH2B02TI4KBTI3HL21Y2Y0S4LST03LCH2B04KBT04KCT03SHB3SHL4CEIL2LO2T13BL11HS2L03LCH2B04KBT04KCT03SHB3SHL4CEIL2LO2T12L13BL13TAL2TI4KBTI3HL21Y2Y0S2L04LEN03LCH3HL21Y2Y0S2L03LCH2B04KBT04KCT03SHB3SHL4CEIL2LO2T12L13BL1S4LST03LCH2B04KBT04KCT03SHB3SHL4CEIL2LO2T13BL11HS2L04LEN03LCH3HL21Y2Y0S3TAL3LCH2B02TI4KBTI3HL21Y2Y0S3LCH3HL21Y2Y02Y1S2L03LCH2B04KBT04KCT03SHB3SHL4CEIL2LO2T12L13BL1S2L04LEN03LCH3HL21Y2Y0S4LEN03LCH3HL21Y2Y02Y1S4CEIL2LO2T13LCH2G42TI3HL21Y1HS4CEIL2LO2T13LCH2B03BL12G42TI3HL21Y2Y01H1N2G33RUPS4CEIL2LO2T14LEN03LCH2G42TI3HL21Y1HS4CEIL2LO2T14LEN03LCH2B03BL12G42TI3HL21Y2Y01H1N2G33RUP2L02L1S4CEIL2LO3LCH5GLST04KBT04KCT03SHB3SHL3Hsp2T14KBTI4KCTI4KDTIS4CEIL2LO3LCH5GLST04KBT04KCT03SHB3SHL3Hsp2T14KBTI4KCTI4KDTIS4CEIL2LO3LCH2G34KBT04KCT03SHB3SHL3Hsp2T12G4S4CEIL2LO3LCH2G34KBT04KCT03SHB3SHL3Hsp2T12G4S4CEIL2LO2T14LST03LCH3BL1S4CEIL2LO2T14LST03LCH3BL1S4CEIL2LO2T12L13LCH3BL1S4CEIL2LO2T12L13LCH3BL14LST0S4CEIL2LO2T12L13LCH3BL1S3HspFS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS4CEIL2LO2T13LCH2B03BL12TI3HL21Y1H2H0S4CEIL2LO2T14LEN03LCH2B03BL12TI3HL21Y1H2H0S4CEIL2LO2T13LCH2B03BL12G42TI3HL21Y2Y01HS4CEIL2LO2T14LEN03LCH2B03BL12G42TI3HL21Y2Y01HS3LST3LCHS3LST3LCHS3LST3LCHS3LST3LCHS3LST3LCHFFFSS3LCH3HspS3LCH3HspS3LCH3HspS3LCH3HspFFS1N2QB3LCHS1N2QB3LCHS1N2QB3LCHS1N2QB3LCHS3LCH2B03BL11HS3LCH2B03BL11HS3LCH2B03BL11HS3LCH2B03BL11HS3LCHS3LCHSS3LCHSS3LCHFFS1N3LCH3QB14KBTI3HL23RUP2KDS1N3LCH3QB14KBTI3HL23RUP2KDS1N4LEN03LCH3QB14KBTI3HL23RUP2KDS1N4LEN03LCH3QB14KBTI3HL23RUP2KDS1N3LCH3QB14KBTI3HL23RUP2KDS1N4LEN03LCH3QB14KBTI3HL23RUP2KDS3LCHS3LCHSS3LCHSS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3BL1S3LCH3BL1S3LCH3BL1S3LCH3BL1S3LCH3BL1SFFFFFS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3LCHS3LCHSS3LCHSS3LCHFS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHFS3NB13LCHS3NB13LCHS3NB13LCHS3LCH2HBS3LCH2HBS3LCH2HBS3LCH2HBS3LCH2HBFS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHFS4LST03LCH2B04KCTI4KDTIS4LST03LCH2B04KCTI4KDTIS2L03LCH2B04KCTI4KDTIS2L03LCH2B04KCTI4KDTI4LST0S2L03LCH2B04KCTI4KDTISS3BSZ3LCHS3BSZ3LCHS3BSZ3LCHS4LST03LCH2B04KCTI4KDTIS4LST03LCH2B04KCTI4KDTIS2L03LCH2B04KCTI4KDTIS2L03LCH2B04KCTI4KDTI4LST0S2L03LCH2B04KCTI4KDTIS4CEIL2LO3LCH5GLST04KCTI4KDTI3HspS4CEIL2LO3LCH5GLST04KCTI4KDTI3HspS4CEIL2LO3LCH2G34KCTI4KDTI3HspS4CEIL2LO3LCH2G34KCTI4KDTI3HspFF".
band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148232192 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (b, b + 8192);      (* [comment removed for export] *)
              (0x9db88, 0x9db88 + 4); (0x9db90, 0x9db90 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof QK as QK0. rw_split QK0 1%nat QMX QK2. clear QK2.
  box DHT. box DTB. box DTL. box DBL. box DHB. box DHL.
  destruct BJ as [junkb BJ].
  destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]];
  unfold dk_glst in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  destruct DK as (MX & GC & GNB & GQB & GFST & GLST & DK');
  (destruct (g_drain g) eqn:EGD;
   [ destruct DK' as (QB1 & GQ & GFULL);
     destruct (g_full g) eqn:EGF;
     [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]
   | rename DK' into QB1 ]);
  rewrite ?EGD in *; cbn [ek_pre dk_pre ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x354d0) (Z_to_bv 64 0x9daf0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0x9db88, 0x9db88 + 4); (0x9db90, 0x9db90 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x354d0) (Z_to_bv 64 0x9daf0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0x9db88, 0x9db88 + 4); (0x9db90, 0x9db90 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box LA0. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_from_refill_spec true t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x354d0) (Z_to_bv 64 0x9daf0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x354d0) (Z_to_bv 64 0x9daf0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0x9db88, 0x9db88 + 4); (0x9db90, 0x9db90 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box FRE. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX FRE CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x354d0) (Z_to_bv 64 0x9daf0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0x9db88, 0x9db88 + 4); (0x9db90, 0x9db90 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX. box FRE.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_norecycle_spec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| lia| lia
      | exact QMX| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX FRE.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia). clear MUd WMd.
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box HD. box CH. box SH'. box FRP.
    snapshot [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_from_refill_spec false t lst b RNG _ _ _ _ _ _ _
               (Z_to_bv 64 0x354d0) (Z_to_bv 64 0x9daf0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 n) a3 (Z_to_bv 64 (t + 208)) (Z_to_bv 64 hm)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt spacebeg lo maxc csz stj idxw chunks j0);
      [unboxed ST| exact CEIL| lia| lia| exact MI| exact FRE| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    replace (bv_unsigned sp + -144 + 64) with (bv_unsigned sp + -80) in * by lia.
    clear ST. match goal with H : stk asegs ?mm lo (bv_unsigned sp + -80) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia). carry SH' MUe WMe ltac:(lia). carry FRP MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [exfalso; unfold Q_CACHE in *; lia|].   (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    do 10 step.
    release_frame FRP ST (bv_unsigned sp).
    unfold put_tail_post. rewrite ?QZE. unfold tcache_post, dk_post, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
