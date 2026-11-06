(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA SysStepF StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase ABytes AKit AKit2 AModelFacts APrimFacts ASecFacts
     ADepot_iface ARep ARepFrame F_ammap F_apoison F_apoison0 APoisonR_iface F_aalloc2 F_aalloc2g.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
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
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
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
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6250496 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6250496 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148232192 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=29376364801.838731552529.800000<00ES1H2H12A82H0S1H2H12A8".
destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma gaas_sec_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (a SB ms needed idx : Z),
  rw_cells asegs m 0x9d838 [C8 (Z_to_bv 64 SB)] ->                         (* [comment removed for export] *)
  rw_cells asegs m 0x9d858 [C8 (Z_to_bv 64 4096)] ->                       (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 needed); C8 (Z_to_bv 64 idx)] ->   (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= needed <= ms -> 8192 <= ms -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) ->
  rng_aimg RNG -> rng RNG a 32 ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 ((needed + 4095) / 4096 * 4096)) s1
                    (Z_to_bv 64 4096) (Z_to_bv 64 (needed + 4095)) (Z_to_bv 64 needed) a3 a4 a5 a6 a7
                    (Z_to_bv 64 (a + 4096)) s3 s4 s5 (Z_to_bv 64 AINSTANCE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x31698) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (a + 4096)) s3 s4 s5 (Z_to_bv 64 AINSTANCE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x31608) fc None m (seg_rom asegs)).
Proof.
  intros until idx. intros I32 I64 HDR AL LO HI ND MS SB0 SBH DJ RIMG RA. pose proof (ablk_lin _ _ LO) as (ALO & AZ0 & _ & _).   (* [comment removed for export] *)
  unfold AINSTANCE in *.
  pose proof HDR as HDR0. rw_split HDR0 2%nat HDRa HDRb. Local Ltac2 Set LiaHints.tbl := fun () => "00M0>1234293436.63 1234293436.64 1259278812.64 1259278812.65 1261375962.68 1261375962.69 1267003993.57 1267004120.57 1267004120.58 1267004378.56 15615277954.5617208403286.5817208403286.5928922925488.5728922925488.5833051290161.2 35231704315.5835714190898.8 46220149566.5746220149566.5848193359221.5753208084950.6653208084950.6753210640358.5753210640358.5857353982691.5659314873579.1465767170219.6465767170219.6500000100200>00I00U00`00k01701B01M01V01W01X01Y01Z01^01_01`01a01b01k02602D02Q02a02b02o030031SSS3SBH3AZ02K0S2HI2MS3AZ0S3SBH3AZ02K0S2HI2MS3AZ0S2HI2MS3AZ0S3SBH3AZ02K0S2HI2MS3AZ0S2HI2MS3AZ0S3SB03SBHSSSSS2ALSSSSS3SB03SBHS2HI2ND3AZ0S2HI2ND3SB02K1S2HI2ND3AZ01HS2HI2ND3SB02K11HSS2MS2DJ2K02K1SS".
rw_split HDRb 1%nat HDRs HDRc. clear HDRa HDRc.
  replace (a + Z.of_nat (cells_size [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms)])) with (a + 16) in HDRs by (cbn; lia).
  lstep.                                                         (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.                               (* [comment removed for export] *)
  2: step; zstep; zstep; step; if_cases K1; zify_cond K1.        (* [comment removed for export] *)
  3: { exfalso. clear -K0 K1 DJ ND ALO HI AL MS; lia. }
  (* [comment removed for export] *)
  all: lstep.                                                    (* [comment removed for export] *)
  all: zstep; zstep.                                             (* [comment removed for export] *)
  all: step; if_cases K2; [zify_cond K2| clear K2].              (* [comment removed for export] *)
  1,3: exfalso; apply K2; change 4095 with (2^12 - 1); rewrite zb_land_mask_l by lia; change (2^12) with 4096; clear -AL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  all: zstep; step; if_lit.                                      (* [comment removed for export] *)
  all: zstep.                                                    (* [comment removed for export] *)
  all: setreg 12 (Z_to_bv 64 a) ltac:(f_equal; lia).
  all: lstep.                                                    (* [comment removed for export] *)
  all: zstep; zstep; zstep.                                      (* [comment removed for export] *)
  all: setreg 8 (Z_to_bv 64 ((needed + 4095) / 4096 * 4096)) ltac:(rewrite land_align4096 by lia; f_equal; clear -ND MS HI ALO; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  all: step.                                                     (* [comment removed for export] *)
  all: apply evtF_done; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wpiece_ok (iv : Z * Z) : Prop := AIMG_HI <= fst iv \/ (0x172d48 <= fst iv /\ snd iv <= 0x5c2d90).

#[using="Type"] Lemma disjoint_img2 : forall W A n, Forall wpiece_ok W -> 0 <= n ->
  (A + n <= 0x172d48 \/ (0x5c2d90 <= A /\ A + n <= AIMG_HI)) -> disjoint_from W A n.
Proof.
  intros W A n HW Hn HA. unfold wpiece_ok, AIMG_HI in *. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>68595141598.11000007S2H12HA".
split; [lia| exact IH].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma poison_cells_frame2 : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' -> Forall wpiece_ok W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW. unfold poison_cells in *. destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_img2; [exact HW| cbn; lia| cbn; unfold AIMG_HI; lia]]).
Qed.

#[using="Type"] Lemma premap_cells_frame2 : forall m m' W,
  premap_cells m -> munch W m m' -> wmono asegs m m' -> Forall wpiece_ok W -> premap_cells m'.
Proof.
  intros m m' W PC MU WM HW. unfold premap_cells in *. destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_img2; [exact HW| cbn; lia| cbn; unfold AIMG_HI; lia]]) ].
Qed.

#[using="Type"] Lemma arelro_frame2 : forall m m' W,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) -> munch W m m' -> Forall wpiece_ok W ->
  forall i, ARELRO_LO <= i < ARELRO_HI -> m' (wa i) = None.
Proof.
  intros m m' W RR MU HW i Hi. rewrite <- (RR i Hi). pose proof (MU (wa i)) as E.
  unfold ARELRO_LO, ARELRO_HI in Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0040>42095072538.1064849878325.1066259835913.106757834505.10 00000400500900:S2HiSS2HiS".
rewrite wa_unsigned in E by lia. apply E.
  eapply disjoint_outside with (a := i) (n := 1); [| lia]. apply disjoint_img2; [exact HW| lia| unfold AIMG_HI; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma land_lnot7_eq : forall n, 0 <= n -> Z.land n (Z.lnot 7) = n - n mod 8.
Proof.
  intros n Hn. rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). Local Ltac2 Set LiaHints.tbl := fun () => "0020=29784460672.350056973662.3000001002SS".
rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section WithDepot.
Variable DI : ADepotIface.
(* [comment removed for export] *)
Hypothesis PR : poison_remap_stmt.

(* [comment removed for export] *)
Notation allocBC_WS L sp a ms :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (a + 6128, a + 6144);
    (shad a + 512, shad a + ms / 8);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocBC_postS (L : alayout) (RNG : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t a ms lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6,
    let AB := a + 4096 in let UB := a + 6144 in
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x31778) fc None m' (seg_rom asegs)
    /\ fp_le RNG RNG'
    /\ munch (allocBC_WS L sp a ms) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (a + 6128) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (hdr_b1_mid 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
       (* [comment removed for export] *)
    /\ fill_at m' (shad a + 512) 256 0xfa
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' (shad UB + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))])
    /\ fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa
    /\ ADEPOT DI L m' /\ poison_cells m' /\ premap_cells m'.

#[using="PR"] Lemma allocBC_sec : forall (L : alayout) RNG (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t a ms idx SB lo sz pc : Z) (tb : list word) (tr : list Z) (fr0 : list byte)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  let AB := a + 4096 in let UB := a + 6144 in let size := needed_size n in
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false -> ms = sec_map_size n ->
  (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= t \/ t + 4096 <= a) -> (a + ms <= al_ctx L \/ al_ctx L + 65536 <= a) ->
  (a + ms <= al_nodes L \/ al_nodes L + 1048576 <= a) -> (a + ms <= al_store L \/ al_store L + 8388608 <= a) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (a + 6128) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (shad AB) [CB 256 (repeat (Z_to_bv 8 0) 256)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))] ->
  (n mod 8 <> 0 -> rw_cells asegs m (shad UB + shlen (n - n mod 8)) [C1 (Z_to_bv 8 0)]) ->
  (exists junk, rw_cells asegs m (shad UB + granules n) [CB (Z.to_nat (ms / 8 - 768 - granules n)) junk]) ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m 0x9e6cd [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells asegs m 0x9d838 [C8 (Z_to_bv 64 SB)] -> rw_cells asegs m 0x9d858 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  sclr t 4096 -> sclr (al_ctx L) 65536 -> sclr (al_nodes L) 1048576 -> sclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG a ms -> rng RNG (shad a) (ms / 8) ->
  (* [comment removed for export] *)
  (forall RNG' m' id rax t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6',
     allocBC_postS L RNG sp gp tp F fc n S t a ms lo m RNG' m'
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 size) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6'
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x31778) fc None m' (seg_rom asegs)) ->
     0 < id < 2^31 ->
     implS asegs RNG' (aembed ATOP k) (epostF Q)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 size) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6'
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x31778) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 UB (Z.land n (Z.lnot 7)) k)) (epostF Q)
    (MS (mkR (Z_to_bv 64 0x314cc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x314cc) fc None m (seg_rom asegs)).
Proof.
  intros until s11v. cbv zeta.
  intros ST CEIL LO MI TP N PRIM HMS AAL ALO AHI DJSB SB0 SBH DJT DJC DJN DJS FR HDRP HDR SHL SHU SHP [junkT SHT] PC PMC RELRO PP I32 I64
         CT8 TT0 CX0 CX1 T0 T1 SHT0 SHC SHN SHS SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1
         RIMG RSTK RS RNO RST RCTX RT RA RSA KONT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, AREQMAX in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "0870?10313444268.4  10337121125.4  1047820382.24  1048143380.18  10495213693.25810495213693.26010625553216.24 10900942429.18911275736598.21311277831256.19311436779546.19011436779546.19311475741760.5  11724964101.11 11799361125.19011799361125.19311801586693.25811801586693.25911801586693.26011801586693.27211801586693.27411807744665.17912226055256.19312428150072.21712428150072.23212428150072.23412428150072.24812428150072.2501261375960.187 1261375960.209 1261375961.223 1267004378.173 12725679640.19312735967027.19313163206680.20913313577562.3  1343986644.199 13539776408.2091370718544.2   1384849688.209 13918739985.16 14153325838.19314218488609.0  14294944825.20714620109034.21714620109034.23214620109034.23414620109034.24814620109034.25014667673607.20614815340875.18914815340875.19214859385738.4  14863574386.21714863574386.24814863574386.25015040422555.5  15513284846.19 15948676913.4  16760036534.25816760036534.26016947070035.12 17023645528.19317289409264.3  1728976368.23  17302731570.3  17379367262.19317833946714.3  17986879152.16 17986879152.19 17986879152.23 17986879152.24 18232594273.21718430975599.18818546653863.4  18930958230.16 19547545880.19319667981417.19019682054918.24 19838492861.25819838492861.26019838492861.27219838492861.27420126411672.19320158040118.20420322563816.3  21195996626.17621230054304.18 21607629932.17521661285377.23221661285377.23421665473273.5  21676762867.19321855607832.1  21864371342.19021864371342.19322269405114.20922290347171.21822290347171.23322290347171.23522290347171.24922290347171.25122466674869.16 22466674869.22 22466674869.23 22470722865.2  2250029779.12  226107864.190  226107864.193  22859182236.26022859182236.27422859556215.3  22916904242.19823015924090.19323171369481.18723171369481.19023236886394.19323410881018.19023410881018.19323449374424.19023449374424.19323549655718.18 23744842134.21823779009444.22 23873206569.19023977376382.19023977376382.19324135553113.19124211191904.4  2431149150.2   2431248216.176 24346898045.25824346898045.26024487705898.17624702500766.17 24841518808.19024841518808.19324982578737.1742503322218.260 2503322218.274 2503999361.2   25076071819.21725076071819.21825076071819.23225076071819.23325076071819.23425076071819.23525076071819.24825076071819.24925076071819.25025076071819.25125157604214.24 25707816664.19025707816664.19325896974040.19025896974040.1932597469155.204 25996042971.24 26326327891.12 26331542390.4  26505308628.2092671846659.18  26954911415.35 27230195271.19027329625324.29 27624122904.20927685599638.24927685599638.25127818598357.5  27822784813.23227822784813.23427943014742.4  27983131173.11 28040491972.21828040491972.23328040491972.23528040491972.24928040491972.251280600266.3    28076054547.4  28485987241.18928580268750.20929782367974.1752980339891.209 29965292900.22 30008181843.12 30162495879.18630162495879.18730162495879.19030242941139.12 30340667940.4  30430348547.18530613629521.17630665193763.21830665193763.23330665193763.23530665193763.24930665193763.25130965447704.19331502080094.4  319281823.190  319281823.193  31948835639.6  32383107196.21732383107196.24832383107196.25032387309188.4  32405727701.20533062543571.16 33062543571.19 33875467557.16 33875467557.19 33875467557.23 3392152800.186 34025853673.18834025853673.19134028498699.3  34074926815.19334309955870.18 34326450181.2  35289778563.18835800809835.21735895327997.25835895327997.26035895327997.27235895327997.27436380301592.19336635088727.17736702058843.17636997264490.30 37152342727.30 37152342727.35 37308521079.3  37308895132.26037308895132.27437549041176.19337937718111.20938211532019.29 38467250200.20938599132038.29 38679500823.22 38903098019.21838903098019.23338903098019.23538903098019.24938903098019.25139175643045.5  39389421077.30 3948396147.190 3948396147.193 39558840408.1933969421227.192 3969782872.193 39784923929.23 40149740076.11 40243014947.21840243014947.23340243014947.23540243014947.24940243014947.25140864623135.4  41105103128.20941320706122.3  41668641880.19341674848079.24841674848079.25041790580420.16 4235737549.23  42363305199.10 42373657203.21842373657203.23342373657203.23542373657203.24942373657203.251423940875.3    42400683642.19342677208786.17642728582814.19342805740039.21742805740039.23242805740039.23442805740039.24842805740039.2504281339941.23  43201035992.19043201035992.19343296826091.19243458394131.22 43477363796.18 43859917978.22 44030571934.2  44375958483.12 44484923210.25844484923210.25944484923210.27244484923210.27344773505040.1  44825444312.19044825444312.19344994127980.30 44994127980.35 45868921845.26045868921845.27445983794898.3  46298861963.18747002354919.5  47006554655.23247006554655.23447486659288.30 47875581774.19348199399523.21848199399523.23348199399523.23548199399523.24948199399523.25148201163096.19348300959827.12 48546482456.19348738442331.17648789606923.3  49160388719.2  49601139032.19349610168957.25849610168957.26049610168957.27249610168957.2745012564595.226 5012564595.228 5014762506.213 5014762506.215 5014762506.229 5014762506.231 50475877991.6  50484222296.19350734000704.19950989421825.3  51121896413.18951458250793.20651469190682.12 51669476109.25851669476109.26051669476109.27251669476109.27452155541549.23252155541549.23452159739605.5  52569147371.12 52569147371.18 52577538839.19052577538839.19352577538839.20952579502455.1995261076886.228 5261076886.230 5310276744.5   53256612379.3  53257845651.16 53258480664.3  53493744851.19553601867864.19353676071172.5  54224864146.23 54404701703.19954405951704.19054405951704.19354963389250.2  54963585858.2  55083526051.21855083526051.23355083526051.23555083526051.24955083526051.25155154452950.19 55260346462.23355260346462.23555295759896.19355365500621.30 55365500621.35 55931979578.19356102654486.20456170256219.19856170256219.21356170256219.21556170256219.22956170256219.23156170498639.17656172251426.22656172251426.22856414764819.12 56442969136.26056442969136.27456443341275.2  56834639827.12 56956174629.24 57022093363.23 57182161452.5  5750404535.209 57628698627.10 57628698627.9  57685397753.19157937621272.20958369413804.2  58477402019.21858477402019.23358477402019.23558477402019.24958477402019.25158683465074.5  58937139502.25758937139502.25959218010518.24459218010518.24659308548964.3  59308628566.4  59308628695.4  59314873579.12 59314873579.13 59586081466.2046067700632.209 6076365731.218 6076365731.233 6076365731.235 6076365731.249 6076365731.251 61030582595.6  61482382924.17861512160097.2  61545466601.20661696339608.19361884732010.22661884732010.22861937685145.18661939782289.18861939782290.23761939782290.23962560701063.19063136544723.12 6316173582.4   63233037343.19363632204029.25863632204029.26063632204029.27263632204029.27463706087133.2  640991434.3    64288705228.25864288705228.25964698966786.19 6483908899.11  65128844401.19 65128844401.23 65145068681.3  65173864152.19065173864152.19365188488701.25865188488701.26065188488701.27265188488701.27465204828578.18865212743211.20865554819096.19365686391930.20966028155702.18066028155702.19966028155702.21466028155702.21666028155702.23066028155702.23266034437902.7  66297517206.21766297517206.24866297517206.25066301708910.4  66311681027.12 66330205174.22 66330498723.18766400267093.18666400267094.18566402364253.18966437773091.21866437773091.23366437773091.23566437773091.24966437773091.25166487633944.20967306296563.29 67420441091.23 6745500894.209 67462911095.13 67469470029.41 67941244093.17968433853656.19068433853656.19368637006742.21768637006742.24868637006742.25068641195374.4  709020802.5    7479973002.18  7522700707.35  7629584909.5   7848643581.258 7848643581.260 7848643581.272 7848643581.274 798746002.260  798746002.274  8047462936.209 8116721570.187 8929152288.175 8935173665.223 9405451517.258 9405451517.260 9405451517.272 9405451517.274 9592678770.29  9630186726.232 9630186726.234 9674728726.197 00000100600=00B00h01N01S01`01i02702\03A03B03C03L03U04`05G06?07=08T09N09\09]09^09_09`09a0:;0:U0:o0;I0;W0<80<F0<G0<H0<V0<[0<i0<o0=T0=U0=c0>i0?n0A80BE0CS0C\0Ch0D40D50D60D70D80DA0D]0D^0EE0El0F=0FK0FO0F^0F_0Fh0Fi0Fo0G50G;0GA0Gk0H40H90H:0HH0HQ0HV0H_0IE0IN0J40JB0JC0JH0JI0JN0K80K90K:0K;0K\0K]0LB0Lg0N<0N_0OQ0PC0Pf0QI0QS0Qc0R30R80RI0RW0Re0Rf0Rg0Rh0SR0T70T@0TI0U^0W30XH0XV0Xd0Y@0Z20ZC0ZL0ZU0Z^0Zl0Zm0[00[;0[a0\G0\P0]30]A0]O0]X0]e0^20^30_10`G0aL0bY0c_0e10f60gK0hQ0ic0ij0j80jF0jT0jb0jk0k00kA0kB0kK0kP0kg0l00l10l?0m50mk0ml0mm0mn0mo0nB0o@10911;12@13F13G13H13Q14614?14`14c14d14m15615?15P15Q15Z15c16F17817j18M19019>19?1:H1;Q1;R1<81<a1=O1=P1=]1=^1=_1=c1=g1=k1>41>B1>P1>U1?^1?g1?l1@51@B1@h1AN1Ad1BJ1BX1C51C@1CM1C^1Cg1Ch1Ci1Cj1D81EA1EL1EZ1Ea1Eb1FE1G71Gi1HL1Ho1I01Ia1JB1Jc1K11K=1KK1KP1Kc1LF1M81Mj1NM1O01O91OG1OH1OV1PG1Q91QD1Q[1Qj1RM1S?1T11TT1U71U<1Ua1Ub1Uk1Ul1Um1Un1Uo1V01V41VB1VP1V\1W31W81WO1WR1Wc1XC1Xc1YC1Yc1Yd1Z21Z@1Zm1[V1[W1[X1[]1[f1[g1\P1]61]U1^:1^]1_O1`A1`d1aG1aU1af1b41b?1bD1bE1bS1c91c_1d51d[1eO1fD1fm1gS1hD1i61i71iE1j=1j>1jK1k51kO1kX1l>1lG1lm1ln1lo1m01mA1m]1mf1mo1n81o01o91oB1oG1oH1oI1oO1o\1oj1ok20:20;20I20W20[20_21B22422f23I23l24324V25925G25^26527J27W27d28128>28K28X28a28j29329D29E29F29G29X29\29]29^29k2:72:C2:Q2:_2:b2;E2<72<i2=L2=o2>02>12>22>;2>D2>K2>R2>Y2>b2>n2?72?E2?h2@Z2AL2Ao2BR2BS2B\2B]2Bf2C42CQ2D>2DI2DT2D_2Dj2E32ED2EE2FN2G42GZ2H02HV2HW2HX2IS2JK2J[2J`2Ja2KA2KF2KT2Kb2LH2Ln2MD2Mj2N32N?2NM2O22OO2Ol2PI2Pf2QC2Q`2Qo2R02R12R22R32RD2RU2Ra2Rn2S;2SH2Sk2T]2UO2V22VU2Vc2Vh2WF2WO2Wb2Xk2Yk2Z92ZG2ZH2ZI2ZJ2ZK2ZT2ZY2Z^2Z_2[E2[k2\A2\g2]U2^F2^T2^]2_G2`92`_2aE2a[2bA2bG2bT2ba2bjSS3AALS2N12R1S3SB0S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG63SG9S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS3SZBS3LTB3MSB3AZ0S3LTB3AZ0S3LTB4ALO13AZ0S4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdS4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdSSS3LTB3AZ0S3LTB3AZ0S3LTB3AZ03SG51N2NB3RSE3RSR3NSE3MSB3SG63SG92M03SG74ASDa4ASDb4CEIL2LO3SG43SPSS4CEIL2LO1N3LTB3MSB3AZ03SG43SG73GLT3SPSS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG83SG93GLT3SG74ASDa4ASDbS3LTB3AZ03SG51N2NB3RSR3NSE3MSB2BG3RSE3MSR3SG73SG94ASDa4ASDb2M0S3LTB3AZ02BG3GLT1N2NB3RSE3RSR3NSE3MSB3SG83SG93MSE3MSR5ABNDb5ABNDc3SG33SG43SG74ASDa4ASDbS1N2T03LTB2NB3RSE3RSR3NSE3MSE3MSB4ALO13AZ03SG92K02K22K32DXS3LTB4ALO13AZ0FFFFFS1N3LTB3MSB4ALO13AZ05ABNDdS1N3LTB3MSB4ALO13AZ05ABNDdS1N3LTB3MSB4ALO13AZ05ABNDdS1N3LTB3MSB4ALO13AZ05ABNDdS3LTB4ALO13AZ0S4CEIL2LO1N3LTB3MSR3MSB3AZ05ABNDdS3LTB4ALO13AZ0FFS3LTB4ALO13AZ0S3AALS3LTB4ALO13AZ0S4ALO1S4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdSS3LTB4ALO13AZ0S4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ05ABNDd3SG13SG73SG94ASDa4ASDb3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ05ABNDd3SG94ASDa4ASDb3SGX2M03HspS4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ05ABNDd3SG83SG94ASDa4ASDb3SGX3GLT3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ05ABNDd3SG23SG53SG73SG94ASDa4ASDb2M03HspS4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ05ABNDd3SG23SG73SG83SG94ASDa4ASDb3GLT3HspS3LTB3AZ0S3LTB3AZ02HBS3LTB3AZ02HBFFFFS3AAL3SG9S1N3AAL3MSB4ALO13SG53MSM3SG7FS4CEIL2LO1N3LTB3SPS3MSB3AZ03SG43SG53SG7S4CEIL2LO1N3LTB3SPS3MSB3AZ03SG43SG73GLTS4CEIL2LO2N02R01HS3LTB4ALO13AZ0S2M0S1N2NB3MSB4ALO1FS3LTB3AZ0FS4CEILS4CEILS4CEILS4CEILS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG13SG73SG9S3LTB3AZ0S3MSMSS3LTB4ALO13AZ0S3LTB3AZ0S3S47S3LTB3AZ0S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS3LTB3AZ0S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS3LTB4ALO13AZ0FS3HspFS3SBHS1N3LTB2NB3RSR3NSE3MSR3MSB3AZ05ABNDa5ABNDdFFFS4CEIL2LO1N3LTB3MSR3MSB3AZ05ABNDdSS4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdS4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdS1N3AAL3LTB2NB3RSE3RSR3NSE3MSE3MSM3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG53SG63SG92K23SG1S4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS3AAL4ALO1S1N3AAL3MSB4ALO1S1N3AAL3MSB4ALO1S3AALS4CEIL2LO2N02R01HS3LTB4ALO13AZ0S3LTB4ALO13AZ0FFFS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG13SG73SG9S4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdS3LTB3AZ0S3LTB3AZ0S1N3AAL3LTB2NB3RSE3RSR3NSE3MSE3MSM3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG53SG63SG92K23SG1S1N3AAL3LTB2NB3RSE3RSR3NSE3MSE3MSM3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG53SG63SG92K23SG1S1N3AAL3LTB2NB3RSE3RSR3NSE3MSE3MSM3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG53SG63SG92K23SG1S3LTB4ALO13AZ0S3LTB4ALO13AZ0S4CEIL2LO3AHI3MSB4ALO12X12X2S4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG43SG73SG93HspS3AHI3RSR3NSE3MSRS3LTB3AZ0S3LTB3AZ0S3LTB3AZ0S3LTB4ALO13AZ0SS1NS1N3LTB3AZ0S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG63SG9S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS3LTB3AZ0S1N3AAL3RSR3NSE3MSR3MSM5ABNDa5ABNDdS3LTB4ALO13AZ0S3LTB4ALO13AZ0S3LTB3AZ0S3LTB3AZ03SG5S3LTB3AZ03SG5FS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG13SG43SG73SG93Hsp3SPS3NSES4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ05ABNDd3SG13SG73SG94ASDa4ASDb3Hsp3SG23SG43SG53SG6S4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG43SG53SG73SG93SGX2M03Hsp3SPSS4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG43SG73SG93SGX2M03Hsp5ABNDd4ASDa4ASDbS4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG43SG73SG83SG93SGX3GLT3Hsp3SPSS4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG43SG73SG83SG93SGX3GLT3Hsp5ABNDd4ASDa4ASDbS4CEIL2LO1N3LTB3MSB3AZ03SG23SG43SG53SG73Hsp3SPS2NB3RSE3RSR3NSE3SG92M0S4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG43SG53SG73SG93SLX2M03Hsp5ABNDd4ASDa4ASDbS4CEIL2LO1N3LTB3MSB3AZ03SG23SG43SG73GLT3Hsp3SPS2NB3RSE3RSR3NSE3SG83SG9S4CEIL2LO1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG43SG73SG83SG93GLT3Hsp5ABNDd4ASDa4ASDbS2N02R0S3LTB4ALO13AZ0S3LTB4ALO13AZ0S3LTB4ALO13AZ0S3LTB4ALO13AZ0S3LTB3AZ0S3SPSS4CEIL2LO2N02R01HFS3LTB3AZ0S3MSBS3MSB3SG53SG74ASDa4ASDbS3LTB3AZ0SS3LTB4ALO13AZ0S4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG43SG53SG73SG93HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG43SG73SG93GLT3HspFFFFS1N3MSE3MSB3SG73SG9S4CEIL2LO1N3LTB3SPS2NB3RSE3RSR3NSE3MSB3AZ03SG13SG43SG73SG93HspS4CEIL2LO1N3LTB3SPS2NB3RSE3RSR3NSE3MSB3AZ03SG43SGX2M03HspS4CEIL2LO1N3LTB3SPS2NB3RSE3RSR3NSE3MSB3AZ03SG43SG83SG93SGX3GLT3HspS4CEIL2LO1N3LTB3SPS2NB3RSE3RSR3NSE3MSB3AZ03SG23SG43SG53SG73SG92M03HspS4CEIL2LO1N3LTB3SPS2NB3RSE3RSR3NSE3MSB3AZ03SG23SG43SG73SG83SG93GLT3HspSFS3LTB3AZ0S4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdS3LTB3AZ0S4CEIL2LO1N3LTB3MSR3MSB3AZ05ABNDdS1NSS3LTB3AZ0S3LTB3AZ0S3LTB3AZ0S4CEIL2LO2N02R01HFS3LTB3AZ0S3LTB3AZ0S4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS3LTB4ALO13AZ0FS1N3AAL3LTB2NB3RSE3RSR3RSM3NSE3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG73SG92K2S1N3AAL3LTB2NB3RSE3RSR3RSM3NSE3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG73SG92K2FS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG13SG9S1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG92M0S1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG83SG93GLTFS3LTB3MSB3AZ0SSS2LOS2LOS2LOS3LTB3AZ0S3LTB4ALO13AZ0S3LTB4ALO13AZ0S3HspS1N3AAL3LTB2NB3RSE3RSR3RSM3NSE3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG73SG92K2S3MSR3MSBS3MSBS3LTB3AZ0S3LTB3AZ03SG1S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG63SG9S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS1N3LTB3MSB3AZ03SG32BGS1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS3LTB4ALO13AZ0S1N2T02T13LTB3MSB4ALO13AZ02K0S1N3LTB3AZ0S3SG13SG33SG2S3SG23SG33SG53SG7S3SG33SG5FFFS3LTB4ALO13AZ0S1N3AAL3LTB2NB3RSE3RSR3RSM3NSE3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG73SG92K2S4CEIL2LO1HS3LTB4ALO13AZ0S2N02R0SS4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspFS3SG13SG33SG43SG53SG75NBNDa5NBNDb5SBNDa5SBNDb3SG2S4CEIL2LO1N3LTB3MSR3MSB3AZ05ABNDdS4CEIL2LO1N3LTB3MSR3MSB3AZ05ABNDdS3LTB4ALO13AZ0S3LTB3AZ02HBS3LTB4ALO13AZ0S3SG5S1N3RSR3NSE3MSE3MSBS4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS2N11H2R1S3LTB4ALO13AZ0FS3LTB4ALO13AZ0S1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG53SG73SG92M0S1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG73SG83SG93GLTS3AHI3MSB1HS4CEIL2LO3SG43SG71H3GLTS4CEIL2LO3SG31HS4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS3HspS4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdFS3LTB3AZ0FFFFFS2LOS3LTB4ALO13AZ0S3LTB4ALO13AZ0S3LTB3AZ02HBS4CEIL2LO3SG43SG53SG71HS3AALS3MSB3SG53SG74ASDa4ASDbS1NS4CEIL2LO2N02R01HS4CEIL1N3LTB3MSB3AZ03SG43SG53SG7S4CEIL1N3LTB3MSB3AZ03SG43SG73GLTS4CEIL1N3LTB3MSB3AZ03SG43SG53SG7S4CEIL1N3LTB3MSB3AZ03SG43SG73GLTSS3LTB4ALO13AZ0S3LTB4ALO13AZ0S3SG23SG33SG43SG53SG75NBNDa5NBNDb5SBNDa5SBNDbS3SG33SG43SG53SG75NBNDa5NBNDb5SBNDa5SBNDbFFS3MSBS3LTB3AZ0FS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG93SGX2M0S1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG93SGXS4CEIL2LO3SG13SG43SG53SG71H3SG2S4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdS4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS3LTB4ALO13AZ0S4CEIL2LO2N02R01HS3LTB4ALO13AZ0S1N3LTB3AZ0S3HspFS3LTB4ALO13AZ0S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG63SG9S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS1N3LTB3MSB3AZ03SG32BGS1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG53SG73SG92M02BGS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG73SG83SG93GLT2BGS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG93SGX2M0S1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG93SGXS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG53SG73SG92M0S1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG23SG73SG83SG93GLTFS3LTB4ALO13AZ0S4CEIL2LO1N3LTB3SPS2N12R12NB3RSE3RSR3NSE3MSB3AZ03SG93HspFS3LTB3MSB3AZ0S1N3LTB2NB3RSR3NSE3MSR3MSB3AZ05ABNDa5ABNDdS1N3AHI3RSR3NSE3MSR4ALO11HS3LTB3AZ0S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS3LTB3AZ0S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTFFFS4CEIL2LO2N12R11HS4CEIL2LO3AHI3MSB4ALO12X12X2S3LTB3AZ0S3LTB3AZ0S3LTB3AZ0S4CEIL2LO1N3LTB3SPS2N12R12NB3RSE3RSR3NSE3MSB3AZ03SG93HspS3LTB3AZ0S3LTB3AZ0S3SG5FSS1N2SMS3LTB3AZ03IDRS3LTB4ALO13AZ0FS1N2NB3MSB4ALO1FS3LTB4ALO13AZ0S3LTB4ALO13AZ0S2R0S2N0S4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS3AHI1HS4CEIL2LO1N3LTB3MSB3AZ03SG43SG73HspS4CEIL2LO1N3LTB3MSB3AZ03SG43SG73HspS3LTB4ALO13AZ0S4CEIL2LO3SG23SG43SG71HS4CEIL2LO3SG43SG53SG71HS1N3AAL3LTB2NB3RSE3RSR3NSE3MSE3MSM3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG53SG63SG92K23SG1S3LTB3AZ03IDRS3LTB3AZ03HspS3LTB3AZ03HspS3LTB3AZ03HspS3LTB3AZ03HspS3LTB3AZ03HspS3LTB3AZ0S3LTB3AZ0S3LTB3AZ0S4CEIL2LO2N02R01HFFFS4CEIL2LO2N02R01HS2LOSFS3LTB3AZ03IDRS3SG53SG72HqS3SG53SG72HqS3LTB4ALO13AZ0S3LTB4ALO13AZ0S1NS4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspFFFS3LTB3AZ0S3LTB3AZ0S2M02NES2T02K3S2NB2K4S4ALO12K0S3RSR3NSE2K2S3LTB3AZ0S3LTB4ALO13AZ0S4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspSS3LTB3AZ0SS3LTB3AZ0S3LTB4ALO13AZ0S1N3LTB2NB3RSR3NSE3MSB3AZ02M0S1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG83SG92K23GLTS1N3LTB3AZ0S1N3LTB3AZ0S1N3LTB3AZ0S1N3LTB3AZ0S3LTB3AZ0S4CEIL2LO2N02R01HFS1N3AAL3LTB2NB3RSE3RSR3RSM3NSE3MSB3AZ05ABNDb5ABNDc3SG23SG33SG43SG73SG92K2S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG63SG9S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS1N3LTB3MSB3AZ03SG32BGS1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTFSS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG53SG63SG73SG94ASDa4ASDb2M0S1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG73SG83SG94ASDa4ASDb3GLTS1N3MSB4ALO13SG7S3MSBSS1N3RSR3NSE3MSR3MSB4ALO13SG53SG7S3MSES3LTB4ALO13AZ0S3LTB4ALO13AZ0S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG63SG9S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS1N3LTB3MSB3AZ03SG32BGS1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS3LTB3AZ0S3LTB3AZ02HBS3LTB4ALO13AZ0S4CEIL2LO1N3LTB3SPS3MSR3MSB3AZ05ABNDdS4CEIL2LO1N3LTB3MSB3SPR3AZ01HS4CEIL2LO1N3LTB3MSB3SPR3AZ01HS4CEIL2LO1N3LTB3MSB3SPR3AZ01HS4CEIL2LO1N3LTB3MSB3SPR3AZ01HS4CEIL2LO1N3LTB3MSB3SPR3AZ01HS4CEIL2LO1N3LTB3MSB3SPR3AZ01HS4CEIL2LO3SPR1HFFFFS4CEIL2LO2N02R01HS4CEIL2LO3AHI3MSBS2LO3LTB3AZ0S3LTB3MSB3AZ0S3LTB3MSB3AZ0S3LTB3MSB3AZ0S4CEIL2LO1N3LTB3MSB3AZ03SG13SG33HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93SGX3HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS4CEIL2LO1N3LTB3MSB3AZ03SG23SG33HspS3LTB4ALO13AZ0S3SG3S1N3AHI3RSR3NSE3MSR3MSB4ALO11HS3LTB3AZ0S3MSB4ALO12Hx2X12X2S4CEIL2LO2N12R12Hq1H2N02R03MSB4ALO12X12X23SG33SG45NBNDa5NBNDb5SBNDa5SBNDbS1N2T03LTB2NB3RSE3RSR3NSE3MSE3MSB4ALO13AZ05ABNDa3SG92K02K22K32DXS3LTB4ALO13AZ0S3LTB4ALO13AZ0FFFFS3SG53SG7S3AHIS3SG5FS1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG63SG9S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS1N3LTB3MSB3AZ03SG32BGS1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG73SG83SG93GLTS1N3LTB2NB3RSE3RSR3NSE3MSB3AZ03SG73SG83SG93GLT2BGS3LTB4ALO13AZ0S3LTB3AZ0S1N3LTB2NB3RSR3NSE3MSR3MSB3AZ05ABNDa5ABNDdS1N3LTB2NB3RSE3RSR3NSE3MSR3MSB3AZ05ABNDa5ABNDd3SG9S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG63SG9S1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS1N3LTB3MSB3AZ03SG32BGS1N3LTB2NB3RSE3RSR3MSB3AZ03SG33SG93GLTS4ALO1S3LTB3AZ03SGXS3LTB3AZ03SGXS3LTB3AZ0".
pose proof (sec_facts n ltac:(unfold AREQMAX; clear -N; lia) PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB). rewrite <- HMS in MSE, MSR, MSM, MSB.
  word_range sp SPR.
  destruct PC as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7).
  rewrite (land_lnot7_eq n) by (clear -N; lia).
  (* [comment removed for export] *)
  pose proof (ablk_lin _ _ ALO) as (ALO1 & AZ0 & _ & _). unfold AIMG_HI in ALO1.   (* [comment removed for export] *)
  destruct (ablk_int _ _ ALO) as (kA & ABND & ABNDa & ABNDb & ABNDc & ABNDd).        (* [comment removed for export] *)
  assert (SG : shad (a + 4096) = shad a + 512 /\ shad (a + 6144) = shad a + 768 /\ 0x800b6c00 <= shad a /\ shad a + ms / 8 <= 0x10007fff8000
               /\ 0 <= shlen (n - n mod 8) <= granules n /\ granules n <= shlen (n - n mod 8) + 1 /\ 768 + granules n + 256 <= ms / 8
               /\ shlen (n - n mod 8) = (n - n mod 8) / 8 /\ granules n = (n + 7) / 8).
  { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -AAL ABND ABNDa ABNDb ABNDc ABNDd AHI N RSR NSE MSR MSM. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }   (* [comment removed for export] *)
  destruct SG as (SG1 & SG2 & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9).
  destruct (ablk_shad_int _ _ ALO ltac:(clear -AAL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) ltac:(clear -MSB; lia)) as (kS & ASD & ASDa & ASDb & _ & _).   (* [comment removed for export] *)
  destruct (sclr_int _ _ SHN ltac:(clear -N0; unfold AIMG_HI in *; lia) ltac:(clear -N1; lia)) as (kN & NBND & NBNDa & NBNDb).   (* [comment removed for export] *)
  destruct (sclr_int _ _ SHS ltac:(clear -R0; unfold AIMG_HI in *; lia) ltac:(clear -R1; lia)) as (kR & SBND & SBNDa & SBNDb).
  pose proof (munch_refl (allocBC_WS L sp a ms) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box TT0. box CT8. box DJT. box DJC. box DJN. box DJS. box DJSB.
  box SHP. box PMC.
  iprefix.
  snapshot [(a + 6128, a + 6144)]%Z MUh WMh.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (a + 6128, a + 6144); (shad a + 512, shad a + 768);
            (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z MUq WMq.
  step. step. if_cases K0; zify_cond K0. { exfalso. clear -K0 ALO AHI MSR NSE RSR ALO1; lia. }     (* [comment removed for export] *)
  zstep. rewrite RZ. setreg 20 (Z_to_bv 64 (a + 6144)) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  zstep. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. clear -AAL. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  zstep.                                                          (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. clear -K2 NSE RSR MSR AHI ALO N ALO1; lia. }   (* [comment removed for export] *)
  lstep.                                                         (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.shiftr_eq_0 n 32) by (try lia; apply Z.log2_lt_pow2; lia).
  rewrite (Z.shiftr_eq_0 n 48) by (try lia; apply Z.log2_lt_pow2; lia).
  sstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep.                                     (* [comment removed for export] *)
  sstep.                                                         (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 T0 SHT0; lia. }   (* [comment removed for export] *)
  carry TT0 MUh WMh ltac:(with_box DJT lia).
  step.                                                          (* [comment removed for export] *)
  carry CT8 MUh WMh ltac:(with_box DJC lia).
  lstep. zstep. step.                                            (* [comment removed for export] *)
  step. step.                                                    (* [comment removed for export] *)
  clear TT0 CT8.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEP' : ADEPOT DI L mm) end.
  { eapply (adi_frame DI); [exact DEP | exact MUh | exact WMh |].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    intros x Hx. pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2. clear -Hx X1 X2 SHN SHS ALO MSB ALO1. lia. }
  clear MUh WMh. box HDR. box HDRP.
  box SHL. box SHU. box SHT.          (* [comment removed for export] *)
  box FR. box PC1. box PC2. box PC3. box PC4. box PC5. box PC6. box PC7. box PP. box I32. box I64.   (* [comment removed for export] *)
  snapshot (adepot_W L (bv_unsigned sp + -128)) MUd WMd.
  step. call_sp ((adi_put DI) L RNG).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ = 1 + _ => exact SZ
       | |- u64arr _ _ _ _ => exact TB
       | |- length _ = _ => exact LTB
       | |- map _ _ = _ => exact TRF
       | |- In _ _ => exact TRU
       | |- ADEPOT _ _ _ => exact DEP'
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; clear -SPR CEIL LO SPS S47 SZB N0 N1 R0 R1 SHN SHS CX0 CX1 T0 T1; lia
       end.
  all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-DEPOT" G end.
  (* [comment removed for export] *)
  lazymatch goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into IDR end.
  lazymatch goal with H : ADEPOT DI L _ |- _ => rename H into DEP2 end.
  snapshot [(bv_unsigned sp + -128 - 592, bv_unsigned sp + -128); (a + 6128, a + 6144); (shad a + 512, shad a + ms / 8)]%Z MUp WMp.
  carry HDR MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; clear -X1 X2 SPR CEIL LO AHI ALO SHN SHS MSB ALO1; lia).
  carry HDRP MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; clear -X1 X2 SPR CEIL LO AHI ALO SHN SHS MSB ALO1; lia).
  carry FR MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PP MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry I32 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry I64 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry PC1 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PC2 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PC3 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry PC4 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PC5 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PC6 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry PC7 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry SHL MUd WMd ltac:(clear -SPR CEIL LO ALO1 AHI MSB SG1 SG2 SG3 SG4 SG5 SG7 NBND NBNDa NBNDb SBND SBNDa SBNDb N1 R1; dlia).   (* [comment removed for export] *)
  carry SHU MUd WMd ltac:(clear -SPR CEIL LO ALO1 AHI MSB SG1 SG2 SG3 SG4 SG5 SG7 NBND NBNDa NBNDb SBND SBNDa SBNDb N1 R1; dlia).
  carry SHT MUd WMd ltac:(clear -SPR CEIL LO ALO1 AHI MSB SG1 SG2 SG3 SG4 SG5 SG7 NBND NBNDa NBNDb SBND SBNDa SBNDb N1 R1; dlia).
  clear MUd WMd.
  zstep. zstep. zstep.                                           (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small x 4294967296) by lia.
  step.                                                          (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (gaas_sec_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- rw_cells _ _ _ _ => first [exact I32 | exact I64 | exact HDRP]
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => eapply rng_sub'; [exact RA|]; clear -MSB; lia
         | |- _ \/ _ => unboxed DJSB
         | |- _ => atop_facts; clear -AAL ALO AHI N NSE RSR MSR MSE MSB SB0 SBH ALO1; lia
         end.
    all: match goal with |- ?G => idtac "REM-GAAS" G end. }
  cbv beta. intros msG ->.
  setreg 8 (Z_to_bv 64 (ms - 4096)) ltac:(f_equal; clear -MSE; lia).
  (* [comment removed for export] *)
  zstep. zstep.                                                  (* [comment removed for export] *)
  setreg 22 (Z_to_bv 64 (a + 6144 + 8 * granules n)) ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -ALO AHI N NSE RSR MSR ALO1; lia); change (2^3) with 8; rewrite SG9; clear -N AAL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  zstep. step. step.                                             (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 2048) ltac:(f_equal; clear; lia).
  rewrite SG1 in SHL.
  step. call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a + 4096) 2048 256 250 lo (repeat (Z_to_bv 8 0) 256)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG1; exact SHL
       | |- shlen _ = _ => reflexivity
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => first [solve_rng | rewrite SG1; eapply rng_sub'; [exact RSA|]; clear -SG7 SG5; lia]
       | |- _ => atop_facts; clear -SPR CEIL LO AAL ALO AHI MSB N ALO1; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-P1" G end.
  rename POST into ST.
  lazymatch goal with H : rw_cells _ _ (shad _) [CB _ (repeat _ _)] |- _ => rename H into SHL' end.
  rewrite SG1 in SHL'.
  (* [comment removed for export] *)
  zstep. zstep.                                                  (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (ms - 6144 - 8 * granules n)) ltac:(f_equal; clear -SG7 MSB SG5; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. step.                                                    (* [comment removed for export] *)
  assert (SGX : shad (a + 6144 + 8 * granules n) = shad a + 768 + granules n) by (rewrite !shad_div; clear -AAL SG9 N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (SLX : shlen (ms - 6144 - 8 * granules n) = ms / 8 - 768 - granules n) by (rewrite shlen_div; clear -MSM SG7; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  rewrite SG2 in SHU. rewrite SG2 in SHT.
  (* [comment removed for export] *)
  unbox SHP.
  destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
  1: clear SHP.
  2: specialize (SHP M0); rewrite SG2 in SHP; box SHP; carry SHP MUq WMq ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 SHN SHS ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; dlia);
     assert (GLT : shlen (n - n mod 8) + 1 = granules n) by (rewrite SG8, SG9; clear -M0 N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  all: clear MUq WMq.
  all: step; call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        (a + 6144 + 8 * granules n) (ms - 6144 - 8 * granules n) (ms / 8 - 768 - granules n) 250 lo junkT).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SGX; exact SHT
       | |- shlen _ = _ => exact SLX
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => first [solve_rng | rewrite SGX; eapply rng_sub'; [exact RSA|]; clear -SG7 SG5; lia]
       | |- _ => atop_facts; clear -SPR CEIL LO AAL ALO AHI MSB MSM SG5 SG7 N ALO1; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-P2" G end.
  all: rename POST into ST.
  all: lazymatch goal with H : rw_cells _ _ (shad _) [CB _ (repeat _ _)] |- _ => rename H into SHT' end.
  all: rewrite SGX in SHT'.
  (* [comment removed for export] *)
  all: step; zstep; zstep.                                       (* [comment removed for export] *)
  all: rewrite (land_align8_48 n) by (clear -N; lia).
  all: step; if_cases K4; [zify_cond K4; exfalso; clear -K4 NB N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| clear K4].   (* [comment removed for export] *)
  all: step; step; step.                                         (* [comment removed for export] *)
  all: step.                                                     (* [comment removed for export] *)
  all: apply evtF_done.
  all: destruct (Z_lt_le_dec (shlen (n - n mod 8)) 65536) as [SM|BG].
  (* [comment removed for export] *)
  1,3: rewrite (poison0_small R (a + 6144) (n - n mod 8) k) by (first [clear -AAL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | rewrite SG8 in SM; clear -SM N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
  1,2: iprefix.
  1,2: call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (a + 6144) (n - n mod 8) (shlen (n - n mod 8)) 0 lo (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG2; exact SHU
       | |- shlen _ = _ => reflexivity
       | |- _ = 0 -> _ => intros _; exact SM
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- rng _ _ _ => first [solve_rng | rewrite SG2; eapply rng_sub'; [exact RSA|]; clear -SG7 SG5; lia]
       | |- _ => atop_facts; clear -SPR CEIL LO AAL ALO AHI MSB MSM MSR NSE RSR SG5 SG7 N NB ALO1; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- implS _ _ _ _ _ => idtac | |- ?G => idtac "REM-P3m" G end.
  1,2: rename POST into ST.
  1,2: lazymatch goal with H : rw_cells _ _ (shad _) [CB _ (repeat _ _)] |- _ => rename H into SHU' end.
  1,2: rewrite SG2 in SHU'.
  1,2: pose proof (fp_le_refl RNG) as FPLE.
  1,2: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (PMC' : premap_cells mm) end.
  1,3: eapply premap_cells_frame2; [unboxed PMC| exact MU| exact WM|]; unfold wpiece_ok;
       repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; clear -SPR CEIL LO SG3 SHN SHS ALO ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil.
  (* [comment removed for export] *)
  3,4: eapply (PR R k Q RNG) with (lo := lo).
  all: try lazymatch goal with |- evtF _ _ _ _ => idtac | |- implS _ _ _ _ _ => idtac | |- forall RNG' m', _ => idtac
                            | |- _ => rewrite !(unsigned_lit (bv_unsigned sp + -128)) by (clear -SPR CEIL LO; lia) end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- premap_cells _ => eapply premap_cells_frame2; [unboxed PMC| exact MU| exact WM|]; unfold wpiece_ok;
                              repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; clear -SPR CEIL LO SG3 SHN SHS ALO ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil
       | |- forall i, _ -> _ = None => eapply arelro_frame2; [exact RELRO| exact MU|]; unfold wpiece_ok;
                              repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; clear -SPR CEIL LO SG3 SHN SHS ALO ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG2; exact SHU
       | |- _ <= shlen _ => exact BG
       | |- forall RNG' m', _ => idtac
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- forall RNG' m', _ => idtac
       | |- rng _ _ _ => first [solve_rng | rewrite SG2; eapply rng_sub'; [exact RSA|]; clear -SG7 SG5; lia]
       | |- _ => unfold PZR_STACK; clear -SPR CEIL LO AAL ALO AHI MSB MSM MSR NSE RSR SG5 SG7 N NB ALO1; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- forall RNG' m', _ => idtac | |- ?G => idtac "REM-P3r" G end.
  3,4: intros RNG' mR t0r t1r t2r a0r a1r a2r a3r a4r a5r a6r a7r t3r t4r t5r t6r PRP;
       destruct PRP as (FPLE & FBW & MUr & WMr & MIr & STr & SHU' & RSU & PCr & PMC'); rewrite SG2 in SHU'; rewrite SG2 in RSU;
       rewrite (unsigned_lit (bv_unsigned sp + -128)) in MUr by (clear -SPR CEIL LO; lia);
       rewrite (unsigned_lit (bv_unsigned sp + -128)) in STr by (clear -SPR CEIL LO; lia);
       rewrite SG2 in MUr; unfold PZR_STACK in MUr, STr; iprefix.
  (* [comment removed for export] *)
  3,4: lazymatch type of MU with munch ?W ?m0 ?m3 => lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (MU2 : munch W m0 mm) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq SPR SG5 SG7; lia]);
         assert (WM2 : wmono asegs m0 mm) by (eapply wmono_trans; [exact WM| exact WMr]);
         clear MU WM; rename MU2 into MU; rename WM2 into WM end end.
  3,4: lazymatch type of MUp with munch ?W ?m0 ?m3 => lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (MUp2 : munch W m0 mm) by (eapply munch_trans; [exact MUp| eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq SPR SG5 SG7; lia]);
         assert (WMp2 : wmono asegs m0 mm) by (eapply wmono_trans; [exact WMp| exact WMr]);
         clear MUp WMp; rename MUp2 into MUp; rename WMp2 into WMp end end.
  3,4: xport HDR MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport SHL' MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport SHT' MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG6 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport PP MUr WMr ltac:(clear -SPR CEIL LO SG3; lia).
  4: xport SHP MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 GLT ALO1 ASD ASDa ASDb; dlia).
  3,4: destruct PCr as (PC1' & PC2' & PC3' & PC4' & PC5' & PC6' & PC7').
  (* [comment removed for export] *)
  all: replace (ret_pc (Z_to_bv 64 0x316e4)) with (Z_to_bv 64 0x316e4 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  3,4: clear MUr WMr.
  all: first [ lazymatch goal with H : _ mod 8 <> 0 |- _ => fail | _ => idtac end;
               call (partial_specG _ n (a + 6144) (shad a + 768 + shlen (n - n mod 8)) 0 (Z_to_bv 8 0))
             | call (partial_specG _ n (a + 6144) (shad a + 768 + shlen (n - n mod 8)) 1 (Z_to_bv 8 0)) ].
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- _ = shad _ + _ => rewrite SG2; reflexivity
       | |- _ = (if _ then _ else _) => first [rewrite (proj2 (Z.eqb_eq _ _) M0); reflexivity | rewrite (proj2 (Z.eqb_neq _ _) M0); reflexivity]
       | |- rw_cells _ _ 0x98e28 _ => assumption
       | |- rw_cells _ _ 0xa0e78 _ => assumption
       | |- rw_cells _ _ 0xa1b60 _ => assumption
       | |- rw_cells _ _ 0xa06dc _ => assumption
       | |- rw_cells _ _ 0x9e6cd _ => assumption
       | |- rng_aimg _ => first [exact RIMG | unfold rng_aimg; eapply rng_fp_le; [exact FPLE| exact RIMG]]
       | |- ~ _ -> rng _ _ _ => intros _; first [ eapply rng_sub'; [exact RSA|]; clear -SG5 SG7; lia
                                            | eapply rng_sub'; [eapply rng_fp_le; [eassumption| exact RSA]|]; clear -SG5 SG7; lia ]
       | |- ~ _ -> rw_cells _ _ _ _ => first [intros _; assumption | intros NE; exfalso; clear -NE M0; lia]
       | |- _ => atop_facts; clear -SPR CEIL LO AAL ALO AHI MSB MSR NSE RSR N NB SG5 SG7 ALO1; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-PART" G end.
  (* [comment removed for export] *)
  all: try lazymatch goal with H : _ -> rw_cells _ _ _ [C1 (Z_to_bv 8 (_ mod 8))] |- _ => rename H into SHPf end.
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) by
         (eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |];
          repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2;
                                     clear -Hq X1 X2 SPR CEIL LO SHN SHS N1 R1 SG3 SG4 SG5 SG7 ALO AHI MSB ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil) end.
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (PCF : poison_cells mm) by
         (unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)) end.
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (PMF : premap_cells mm) by
         (first [ assumption
                | eapply premap_cells_frame2; [unboxed PMC| exact MU| exact WM|]; unfold wpiece_ok;
                  repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; clear -SPR CEIL LO SG3 SHN SHS ALO ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil ]) end.
  all: apply evtF_done; eapply KONT; [| exact IDR].
  all: unfold allocBC_postS; cbv zeta.
  all: lazymatch goal with |- exists id, _ => exists x end; do 17 eexists.
  all: split; [reflexivity|].
  all: split; [exact FPLE|].
  all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|]. all: split; [assumption|]. all: split; [exact IDR|].
  all: split; [exact HDR|].
  all: split; [unfold fill_at; exact SHL'|].
  all: split; [rewrite SG2; exact SHU'|].
  all: split; [rewrite SG2; first [exact SHPf | intros NE; exfalso; clear -NE M0; lia]|].
  all: split; [unfold fill_at; rewrite SG2; exact SHT'|].
  all: split; [exact DEPF| split; [exact PCF| exact PMF]].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithDepot.
End CANSEC1.
