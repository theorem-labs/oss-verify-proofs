(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase ADepot_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AModelFacts F_memset F_apoison F_aalloc_s.
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
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition hdr_b1_mid (b1 : Z) : Z := Z.lor (Z.land (Z.lor (Z.land b1 18446744073709551612) 1) 143) 16.

Notation allocBC_W L sp UB PG pgw n :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocBC_post (L : alayout) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t AB UB PG pgw lo b0 b1 : Z) (pj : byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x31778) fc None m' (seg_rom asegs)
    /\ munch (allocBC_W L sp UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 (hdr_b1_mid b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

(* [comment removed for export] *)
#[using="Type"] Lemma partial_spec : forall RNG (n UB PG pgw : Z) (pj : byte) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  mem_inv asegs m ->
  1 <= n <= 448 -> PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  ablk UB (UB + n) -> UB + n <= ATOP -> UB mod 8 = 0 ->          (* [comment removed for export] *)
  rw_cells asegs m 0x98e28 [C8 (Z_to_bv 64 0x1329a8); C8 (Z_to_bv 64 0x9e678); C8 (Z_to_bv 64 0xa0e78);
                             C8 (Z_to_bv 64 0xa1b68); C8 (Z_to_bv 64 0xa1b70); C8 (Z_to_bv 64 0xa1b60)] ->
  rw_cells asegs m 0xa0e78 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0xa1b60 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xa06dc [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0x9e6cd [C1 (Z_to_bv 8 1)] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  rng_aimg RNG -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF asegs RNG (fun ms' => exists ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' m',
      ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 UB) s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x31778) fc None m' (seg_rom asegs)
      /\ munch [(PG, PG + pgw)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 UB) s5 (Z_to_bv 64 (n - n mod 8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x316e4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI N HPG HPW UBLO UBHI UB8 GOT SHB LAY CANP PP SHP RIMG RPG.
  pose proof (munch_refl [(PG, PG + pgw)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold ablk, AIMG_HI, KLS in UBLO. atop_facts.                (* [comment removed for export] *)
  assert (SHR : 0x7fff8000 <= shad UB /\ 0 <= shlen (n - n mod 8) <= 56 /\ PG + 1 <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF in *. Local Ltac2 Set LiaHints.tbl := fun () => "00f0>11383758314.6911385855457.7316630097935.6023495003441.5823495003830.6127238478433.5928277756440.5928277756440.6228913119921.7028915217076.6628915217081.7229429014875.5929429014875.6229782367974.5729784416474.6129784417117.5830784453914.5830784454301.6133858871586.5933858871586.623664093147.70 3664093147.74 41385966171.5941385966171.6251298963291.5951298963291.6252076332701.6855019083177.7055019083177.7455034126459.5955034126459.6255148979235.6055148979362.6155148980005.5855148980132.5955157802157.6955157802157.7255919745627.5955919745627.6259308548964.6059308628433.5959308628566.6059308628695.6159588178609.7060802846458.5761884731502.5961929812114.5961929812241.5861929812630.6161937685146.6861939782289.7462027950898.578010146619.59 8010146619.62 00000100200?00@00A00L00P00T00U00V00W00`00i00j00k00l01901D01E01F01G01H01Q01Z01c01l01m01n01o02802A02H02O02e03203D03K03T03]03k04804E04Z04[05205505805;05>05A05D05E05J05OSSS1N4UBLO2K01eSSS1N4UBLO2K0S2HBS2HBSSSS3HPG3SHRS3HPG3SHRSSSS1N3UB82K02K1S3UB82K02K4SSSSS3HPG3SHRS3HPG3SHRS3HPG3SHRS3HPG3SHRFSSS3HPG3SHRS3HPG3SHRS2K12K2S2K12K2S1N4UBLO4UBHI3UB81H2K0S1N4UBHI1H2K1S1N4UBLO3UB82K02K1S2K12K2S3HPG3SHRS3HPG3SHRS1N4UBLO2K02NES1N4UBHI1H2K2S1N4UBHI1H2K3S1N4UBLO3UB82K02K12K4SS1N3HPG4UBLO4UBHI3UB81HS1NS1NS1NS1NS1NS1NSS3SHRS3SHR".
rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  step. if_cases K0; zify_cond K0.                               (* [comment removed for export] *)
  { apply evtF_done. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. intros NE. exfalso. lia. }
  specialize (SHP ltac:(lia)). specialize (RPG ltac:(lia)).
  assert (PW1 : pgw = 1) by (rewrite HPW; destruct (Z.eqb_spec (n mod 8) 0); [lia|reflexivity]). clear HPW. subst pgw.
  step. callp can_poison_spec; [exact CANP|]. step. if_lit.      (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
  step. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  2: step; step; step; step; step; step; zstep.                  (* [comment removed for export] *)
  2: step; if_cases K2; zify_cond K2; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; step; step; zstep; zstep.                             (* [comment removed for export] *)
  2: step; if_cases K3; zify_cond K3; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: step; step; lstep; zstep; zstep.                          (* [comment removed for export] *)
  all: setreg 10 (Z_to_bv 64 PG) ltac:(rewrite HPG; unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; f_equal; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  all: zstep; zstep; zstep.                                      (* [comment removed for export] *)
  all: rewrite (land_ones_r n) by lia; change 7 with (2^3 - 1) at 1; rewrite (zb_land_mask n 3) by lia; change (2^3) with 8.
  all: sstep.                                                    (* [comment removed for export] *)
  all: apply evtF_done; do 11 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
  all: intros _; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".



#[using="Type"] Lemma allocBC_spec : forall (L : alayout) RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (pj : byte) (sj : list byte)
    (tb : list word) (tr : list Z) (fr0 : list byte) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= 448 ->
  (* [comment removed for export] *)
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> sclr t 4096 ->
  (al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) -> sclr (al_ctx L) 65536 ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> sclr (al_nodes L) 1048576 ->
  (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> sclr (al_store L) 8388608 ->       (* [comment removed for export] *)
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 56 -> PG + 1 <= 0x10007fff8000 ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sj] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  poison_cells m -> rw_cells asegs m 0x9e6cd [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->       (* [comment removed for export] *)
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
  rng RNG (UB - 16) 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF asegs RNG (allocBC_post L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
    (MS (mkR (Z_to_bv 64 0x314cc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x314cc) fc None m (seg_rom asegs)).
Proof.
  intros until s11v.
  intros ST CEIL LO MI TP N HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
         SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.   (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "04D0?10313444268.4  1047820382.150 10625553216.15010669833637.17410721241625.16111191675278.2  11308066606.16111345999550.14711345999550.14811752483811.12212428150072.18912480772618.1671324746171.158 1324746171.161 13313577562.3  13336768858.16113367089074.1761343986644.170 14311754318.17714338279425.4  15319906838.17115830019643.16115948676913.4  16334715966.14716334715966.14816346643763.17516486372681.16816512576796.14616528622318.16116545774130.5  16557567661.16616557567661.18117268238158.1611728976368.168 17302731570.3  17833946714.3  17949008832.17117949008832.18617986879152.15017986879152.16818430975599.15918438573326.17719117323662.2  19352503472.16119517033132.16619517033132.18119682054918.15020158040118.1752027029998.177 20322563816.3  20719413306.16121195996626.14721597125182.14721597125182.14821969407398.14722290347171.1902260382799.170 22718042091.16622718042091.16822718042091.18124211191904.4  2431248216.147 24982578737.14525076071819.18925076071819.19025157604214.1502568057522.195 2570154646.180 2597469155.175 25996042971.15026403658112.15826706029342.4  27775112880.4  27943014742.4  27967631154.19527969728278.18028040491972.190280600266.3    28439391382.18028441488562.19528485987241.16028656514152.4  28729582384.5  29079162542.16129731464110.16129782367974.14629782367974.16730236255823.17030430348547.15630507154306.14430517090690.17830613629521.14930665193763.19031192993456.16131366954517.15031919940686.16132377744366.17732475639163.17732769400735.16632769400735.18132932373168.4  33082065689.17733262659552.14733262659552.14833445853437.2  33577178314.14733577178314.14833875467557.1683392152800.157 34028498699.3  34170950174.14734170950174.14834243631625.17234619533406.14734619533406.14834755885818.17735289778563.15936254216601.15736254216601.15836254216601.16136376561033.4  36534319948.4  36635088727.14836702058843.14736967174608.16137032966094.16137774863470.177386431922.195  388529046.180  38903098019.19039332243886.16139523213398.4  39896594704.17741030367075.17241320706122.3  41385801650.19541387898774.18041792303450.16142373657203.190423940875.3    42677208786.14742805740039.18943666138781.4  44386577743.17044820102307.14744820102307.14844820102307.16145122878526.14745122878526.14845221239098.17745480795915.3  45699881561.1614573656713.2   45891680928.18045893778052.19546298861963.15846988300803.12247039319577.16147244432302.14747244432302.14848199399523.19048240491802.16048242588945.15648242588946.15748290080463.17048738442331.14748865763193.2  49181239354.16149793197630.14749793197630.14850645046474.14750645046474.14850734000704.17251046289722.15751048386864.16051683311886.16151816630506.14751816630506.14852523015482.15752567164907.14752567164907.14852567164907.16152567164907.17752569147371.17052579502455.17052579502455.17152682867945.14752682867945.14852736796155.5  53493744851.16654224864146.16854404701703.17055083526051.19055473260884.14655737904206.16155802608718.16155810868206.17756102654486.17556115695737.19556117792861.18056170256219.17056170498639.14956408338831.17056828479823.17056956174629.15057022093363.16857384158754.19557386255878.1805750404535.180 58174797435.16158351610802.19558353707926.18058369446314.16758477402019.19058730541225.18058732638349.19558840920286.16158987689625.17758998195513.1615910326350.161 59218010518.18559314873579.14559314873579.14759314873579.1495932235838.147 5932235838.148 59338331354.16159586081466.17560385159294.1776076365731.190 60795071034.16061482382924.14961671386902.15661673380011.5  61674577390.17761884732010.16761937685145.15761939782289.15961939782290.1786201887545.150 6232988478.147 6232988478.148 6298254074.177 63142967631.1706316173582.4   63999581114.2  64026414714.161640991434.3    64229420110.16164738246334.16164897170030.16664897170030.18164996132282.16065128844401.16865164961555.19065204828578.15965299792814.16165529023470.17766028155702.15366028155702.17166318105247.17066330498723.15867180176575.5  67469470029.15367469470029.44 67519944110.16167713207254.18067715304434.19568398178269.1686896978414.177 6993150894.161 8116721570.158 8256265294.161 8646118925.1   8929938862.161 9674728726.168 00000100800A00B00C00D00R00`00n00o01001101201301401R01S01T01X01Y01j01k01l02:02H02I02n03R03V03W04504S04a05R05S05T07708Z08`08f08g09509609709<09A09F09G09U09Z0:40:50:C0:Q0:U0:j0;=0;Z0<70<T0<U0<X0<Y0=>0>00>70>H0>Y0>Z0>_0?=0?>0??0?@0?Q0?b0@;0@<0@M0@^0@_0@e0@f0A40AB0AC0AD0AW0AX0Ao0BF0BG0B\0C=0Cf0D40DB0DC0DF0DI0DJ0DK0Dl0EM0EN0El0FJ0FN0FO0FT0FX0F\0Fl0G:0GH0Gf0Gg0Gh0Gi0Gj0Gk0Gl0HA0HD0He0I30IA0IR0Ic0J80JF0JN0Jo0K00K10KB0KS0Km0LB0LG0LH0LI0LJ0L]0L^0L_0L`0Ln0M<0M@0ME0M^0M_0NR0OE0OF0OG0OH0Oe0PB0PW0PX0PY0PZ0Pm0Q00Q10QO0Q]0Qk0RE0R_0S60S70S80S<0S@0SD0SE0SF0SG0SH0SI0U70UR0US0Ul0VE0VF0VK0W00W10WF0W]0Wk0X90XG0XL0Xb0Y80Y=0Y>0YQ0Yd0Yh0Yi0Z:0ZK0ZP0ZQ0Zb0[30[60[K0[Z0[i0\F0\_0]80]F0]G0]P0]_0^20^@0^N0^R0^S0_00_E0_F0_G0_K0_L0_Z0`I0`L0`O0`R0a;0aI0aW0b10bD0bE0bF0bJ0bK0bY0c60cG0cX0cY0c^0d70d80dF0dT0dc0e20eE0eI0eJ0fD0gN0g\0gm0h>0hk0i90iG0iH0iV0iW0ie0ifSS2N12R1S3SZB3LTBSSFS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRSFSSSFS3HUB4ABLO3HPG3SB23SB33SB43RZRSFS2HBFS4CEIL2LO3CX13HspSFS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RSR2K21HS1N3HUB4ABLO4UBHI3NSZ2NS3RZR3RSR3NSRS2HBFS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HUB4ABLO3RZRS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RSR3RSM2K02K32K4FFS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RSR3RSM3NSR2K02K32K42NE4SHN04SHS01HS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RSR3RSM3NSR2K02K32K42NE4SHN04SHS01HS4CEILS4CEILSS3HUB4ABLO3RZRFSS3HPGS3HPGS3S47FS3HUB4ABLO3RZRS3HspS3HUB4ABLO3HPG3SB33SB43RZRFS3HUB4ABLO3RZRS3HUB4ABLO3RZRS2B1S4CEIL2LO3SB13SB23HspS4CEIL2LO2N02R03HspS1N3HUB4ABLO4AB163LTB3RZR3RZES1N3HUB4ABLO4AB163LTB3RZR3RZES1N3HUB4ABLO4AB163LTB3RZR3RZESS1NSS4CEIL2LO3HPG3SB23SB33SB43Hsp3LTB3SPSS4CEIL2LO3HUB4ABLO4UBHI3NSZ3HPG3SB42NS3RZR3RSR3HspS2N02R0S3HPG3SB13SB23SB3S3HPG3SB13SB23SB3SS3SPSS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRFFFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S4CEIL2LO3HPG3SB43SPS3HspSS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3SS4AB16SS3HUB4ABLO3RZRS3HUB4ABLO3RZRSSS4CEIL2LO2N02R03HspSS3HUB4ABLO4UBHI3NSZ3NSRS3HUB4ABLO4UBHI3NSZ3NSRSS4CEIL2LO3SB13SB23HspS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS1N3HUB4ABLO4AB162T03LTB3RZR3RZE2K02K32DXS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS1NS1NFSS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRFS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3HPG3SB23SB33SB43RZRS2LOSS3HspS2HBS2HBS4CEIL2LO2T13HspS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB23SB33SB43RZRSSSSFSS1N4ABLO2T02T13LTB2K0S1NS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S4CEIL2LO3SB13SB23HspS3HUB4ABLO3RZRS4AB161HS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRFFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO3SB13SB23HspS3HspFFFS4CEIL2LO2N02R03HspSSSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS2HBS3HspS4CEIL2LO4UBHI3NSZ2NS3RSRSS3HUB4ABLO3SB44PW013RZR3HPG3SB33SB24CEIL2LO3LTB3SPSS3HPG3SB33HUB4ABLO3SB44PW013RZR3SB24CEIL2LO3LTB3SPSSSSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO3SB13SB23HspSSSS4CEIL2LO2N02R03HspS1NFS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO3SPS2N12R13HspSSS2HBS2HBS2HBSSSSSS4CEIL2LO1N3HUB4ABLO4UBHI4AB163NSZ2T03LTB2N12R12NS3RZR3RZE3RSR2K02K32X12X21H3HPG3SB13SB23SB33SB44SHN04SHS03RSMS4CEIL2LO2N12R13Hsp3LTB3SPSFS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRFS3IDRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RSR3RSMFS4CEIL2LO3SB13SB23HspS3HUB4ABLO4UBHI3NSZ3NSRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3IDRS4CEIL2LO3SB43SPS4PW01S4CEIL2LO3SB43SPS4PW01S3HspSS4CEIL2LO2N02R03HspS4CEIL2LO2N02R03HspS2LOSS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3IDRSS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S1NS4CEIL2LO3SB13SB23HspS4CEIL3SB44PW01S4CEIL3SB44PW01S4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS3HUB4ABLO3RZRSS4ABLO2K0S3HUB2NS3RSR2K2S4ABLO2T03LTB2K02K3S3HUB4ABLO3RZRS3HUB4ABLO3RZRS2HBSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO3SB13SB23HspSSS2B1FS3HUB4ABLO3RZRS1N3HUB4ABLO4AB163LTB2NS3RZR3RZE3RSR3RSM3NSR2K2S1NS1NS1NS1N3HUB4ABLO4AB162T03LTB3RZR3RZE2K02K32DXS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO2N02R03HspFFS2HBSS3HUB4ABLO3RZRS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4UBHI3NSZ2NS3RSRS4UBHI3NSZ2NS3RSRSS3SB3S4CEIL2LO3HPG3SB33SB43HspSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO2N02R03HspS2LOFS1N3HUB4ABLO4AB162T03LTB2NS3RZR3RZE3RSM3NSR2K02K32Ha2X12X2S4CEIL2LO2N12R12Ha1H3HUB4ABLO3RZR2X12X24SHN04SHS03HPG3SB13SB23SB43SB34PW01S3HUB4ABLO3RZRS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RZR3RSR3NSR2K21HS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS3HUB4ABLO3RZRSS3HUB4ABLO3RZRS".
assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (UB16 : UB mod 16 = 0).
  { rewrite HUB. pose proof (rz_size_small_cases n N). clear -AB16 H. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  word_range sp SPR.
  destruct PC as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7).
  pose proof (munch_refl (allocBC_W L sp UB PG pgw n) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box TT0. box CT8. box DJT. box DJC. box DJN. box DJS.
  snapshot [(UB - 16, UB)]%Z MUh WMh.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
            (shad UB, shad UB + shlen (n - n mod 8));
            (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z MUq WMq.
  box SHP.
  step. step. if_cases K0; zify_cond K0. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. setreg 20 (Z_to_bv 64 UB) ltac:(rewrite HUB; reflexivity).   (* [comment removed for export] *)
  zstep. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. rewrite HUB, RZE.
       rewrite (rz_log_small n N). clear -AB16 N.
       destruct (n <=? 48); [|destruct (n <=? 96)]; cbn; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  zstep.                                                          (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }              (* [comment removed for export] *)
  lstep.                                                         (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.shiftr_eq_0 n 32) by (try lia; apply Z.log2_lt_pow2; lia).
  rewrite (Z.shiftr_eq_0 n 48) by (try lia; apply Z.log2_lt_pow2; lia).
  sstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep.                                     (* [comment removed for export] *)
  sstep.                                                         (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }             (* [comment removed for export] *)
  carry TT0 MUh WMh ltac:(with_box DJT lia).
  step.                                                          (* [comment removed for export] *)
  carry CT8 MUh WMh ltac:(with_box DJC lia).
  lstep. zstep. step.                                            (* [comment removed for export] *)
  step. step.                                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEP' : ADEPOT DI L mm) end.
  { eapply (adi_frame DI); [exact DEP | exact MUh | exact WMh |].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    intros a Ha. pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2. lia. }
  clear MUh WMh. box HDR.
  snapshot (adepot_W L (bv_unsigned sp + -128)) MUd WMd.
  box SHA. box SHU.          (* [comment removed for export] *)
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
       | |- _ => unfold AIMG_HI; lia
       end.
  (* [comment removed for export] *)
  lazymatch goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into IDR end.
  lazymatch goal with H : ADEPOT DI L _ |- _ => rename H into DEP2 end.
  snapshot [(bv_unsigned sp + -128 - 64, bv_unsigned sp + -128); (UB - 16, UB); (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw)]%Z MUp WMp.
  carry HDR MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; lia).
  carry SHA MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia)). carry SHU MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia)).
  clear MUd WMd.
  zstep. zstep. zstep.                                           (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small x 4294967296) by lia.
  step.                                                          (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. step. step. zstep. zstep.                                (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (shad AB)) ltac:(unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
  lstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. zstep. zstep.                                            (* [comment removed for export] *)
  rewrite (land_align8_48 n) by lia.
  step. if_cases K4; zify_cond K4.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_spec RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0x98e28 _ => exact PC1
         | |- rw_cells _ _ 0xa0e78 _ => exact PC4
         | |- rw_cells _ _ 0xa1b60 _ => exact PC5
         | |- rw_cells _ _ 0xa06dc _ => exact PC6
         | |- rw_cells _ _ 0x9e6cd _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_post. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    (* [comment removed for export] *)
    rewrite K4. rewrite K4 in SHU. pose proof SHU as W0. destruct W0 as [[[WF X1] X2] X3]. cbn in WF. destruct sj; [exact SHU| cbn in WF; discriminate].
  - (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UB (n - n mod 8) 0 lo sj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
         | |- mem_inv _ _ => assumption
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ (shad _) _ => exact SHU
         end.
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- rng _ _ _ => solve_rng
         | |- ablk _ _ => unfold ablk; right; atop_facts; lia
         | |- _ => atop_facts; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]
         end.
    (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_spec RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0x98e28 _ => exact PC1
         | |- rw_cells _ _ 0xa0e78 _ => exact PC4
         | |- rw_cells _ _ 0xa1b60 _ => exact PC5
         | |- rw_cells _ _ 0xa06dc _ => exact PC6
         | |- rw_cells _ _ 0x9e6cd _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_post. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithDepot.
End CANSEC1.
