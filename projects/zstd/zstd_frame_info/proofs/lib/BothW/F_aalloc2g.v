(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase ADepot_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AModelFacts APrimFacts F_memset F_apoison F_aalloc_s.
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

Notation allocBC_WG L sp UB PG pgw n :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocBC_postG (L : alayout) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t AB UB PG pgw lo b0 b1 : Z) (pj : byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x3177c) fc None m' (seg_rom bsegs)
    /\ munch (allocBC_WG L sp UB PG pgw n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 (hdr_b1_mid b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

(* [comment removed for export] *)
#[using="Type"] Lemma partial_specG : forall RNG (n UB PG pgw : Z) (pj : byte) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  mem_inv bsegs m ->
  1 <= n -> PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  ablk UB (UB + n) -> UB + n <= ATOP -> UB mod 8 = 0 ->          (* [comment removed for export] *)
  rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                             C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)] ->
  rw_cells bsegs m 0xa1038 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0xa1d20 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xa089c [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0x9e88d [C1 (Z_to_bv 8 1)] ->
  (n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->
  rng_aimg RNG -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF bsegs RNG (fun ms' => exists ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' m',
      ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 UB) s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x3177c) fc None m' (seg_rom bsegs)
      /\ munch [(PG, PG + pgw)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 UB) s5 (Z_to_bv 64 (n - n mod 8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x316e8) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI N HPG HPW UBLO UBHI UB8 GOT SHB LAY CANP PP SHP RIMG RPG.
  pose proof (munch_refl [(PG, PG + pgw)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold ablk, AIMG_HI, KLS in UBLO. atop_facts.                (* [comment removed for export] *)
  assert (SHR : 0x7fff8000 <= shad UB /\ 0 <= shlen (n - n mod 8) /\ PG + 1 <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF in *. Local Ltac2 Set LiaHints.tbl := fun () => "00f0>11383758314.6911385855457.7316630097935.6023495003441.5823495003830.6127238478433.5928277756440.5928277756440.6228913119921.7028915217076.6628915217081.7229782367974.5729784416474.6129784417117.5830784453914.5830784454301.6133858871586.5933858871586.6234969967195.5934969967195.6235810301874.573664093147.70 3664093147.74 47552575323.5947552575323.6252076332701.6853649105243.5953649105243.6255019083177.7055019083177.7455148979235.6055148979362.6155148980005.5855148980132.5955157802157.6955157802157.7259308548964.6059308628433.5959308628566.6059308628695.6159588178609.7061884731502.5961929812114.5961929812241.5861929812630.6161937685146.6861939782289.7462968635793.57703684731.59  703684731.62  8010146619.59 8010146619.62 9393672027.59 9393672027.62 00000100200?00@00A00L00P00T00U00V00W00X00Y00Z00g01201301401=01F01G01H01I01R01[01\01e01n01o02002702>02T02a03303:03H03U03b04704804G04V04h05:05L05^06506>06G06L06Q06Z06cSSS1N4UBLO2K01eSSS1N4UBLO2K0S2HBS2HBSSSSSSS1N3UB82K02K1S3UB82K02K4SSS3HPG3SHRS3HPG3SHRSSSS3HPG3SHRS3HPG3SHRFS3HPG3SHRS3HPG3SHRSSS2K12K2S2K12K2S1N4UBLO4UBHI3UB81H2K0S1N4UBHI1H2K1S1N4UBLO3UB82K02K1S2K12K2S1N4UBLO2K02NES1N4UBHI1H2K2S1N4UBHI1H2K3S1N4UBLO3UB82K02K12K4SS1N4UBLO4UBHI1HS1N4UBLO4UBHI1HS1N4UBLO4UBHI1H2K0S1N4UBLO4UBHI1H2K0S1N4UBLO4UBHI1H2K0S1N4UBLO4UBHI1H2K0S1N3HPG4UBLO4UBHI3UB81HS3HPG3SHRS3HPG3SHRS3SHRS3SHRS3HPG3SHRS3HPG3SHR".
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



#[using="Type"] Lemma allocBC_gen : forall (L : alayout) RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (pj : byte) (sj : list byte)
    (tb : list word) (tr : list Z) (fr0 : list byte) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  (* [comment removed for export] *)
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> sclr t 4096 ->
  (al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) -> sclr (al_ctx L) 65536 ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> sclr (al_nodes L) 1048576 ->
  (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> sclr (al_store L) 8388608 ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells bsegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sj] ->
  (n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  poison_cells m -> rw_cells bsegs m 0x9e88d [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells bsegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr bsegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF bsegs RNG (allocBC_postG L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
    (MS (mkR (Z_to_bv 64 0x314d0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x314d0) fc None m (seg_rom bsegs)).
Proof.
  intros until s11v.
  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
         SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.   (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "04;0?10054784078.16310194000543.17210313444268.4  1047820382.152 10625553216.15210669833637.17610721241625.16310842551374.16311191675278.2  11480366910.14911480366910.15011752483811.12311925506990.16312270362430.14912270362430.15012428150072.19112480772618.1691324746171.160 1324746171.163 13313577562.3  13336768858.16313367089074.1781343986644.172 13923957822.14913923957822.15014014474241.4  14159447534.17914311754318.17915319906838.17315830019643.16315948676913.4  16346643763.17716486372681.17016512576796.14816528622318.16316545774130.5  16557567661.16816557567661.18316594262294.18216596359474.19716963689266.3  1728976368.170 17601143726.16317833946714.3  17949008832.17317949008832.18817986879152.15217986879152.17018365406014.14918365406014.15018430975599.16119117323662.2  19352503472.16319517033132.16819517033132.18319682054918.1521990225994.3   20158040118.17720322563816.3  20719413306.16320857720078.17921062356398.16321195996626.14921969407398.14922718042091.16822718042091.17022718042091.18322728847957.2  23891548451.19224211191904.4  2431248216.149 24892159950.16324982578737.14725076071819.19125076071819.19225157604214.1522597469155.177 25996042971.15226403658112.16027028261662.4  27775112880.4  27943014742.4  28040491972.19228242461078.17028485987241.16228729582384.5  29021953738.3  29782367974.14829782367974.16929965292900.16829965292900.18330047027402.3  301011343.172  30430348547.15830507154306.14630517090690.18030613629521.15131192993456.16331366954517.15231498178222.16331791172943.17232475639163.17932932373168.4  33082065689.17933262659552.14933262659552.15033445853437.2  33577178314.14933577178314.15033764744995.19233875467557.1703392152800.159 34028498699.3  34170950174.14934170950174.15034243631625.17434755885818.17934779080494.1633495373902.163 35289778563.16135711452879.17236254216601.15936254216601.16036254216601.16336376561033.4  36534319948.4  36635088727.15036702058843.14936967174608.16339518923089.4  39896594704.17940194010222.17940858487054.4  41030367075.17441647040034.19741649137158.18241792303450.16341843714542.179423940875.3    42614983602.19742617080726.18242677208786.14942805740039.19143706322738.19743708419862.18243990206109.4  44052358222.16344820102307.14944820102307.15044820102307.16345221239098.17945480795915.3  4565746606.163 45699881561.1634573656713.2   45891680928.18245893778052.19746298861963.16046988300803.12347039319577.16347244432302.14947244432302.15048240491802.16248242588945.15848242588946.15948738442331.14948865763193.2  49133638259.19249181239354.1635012112366.179 50645046474.14950645046474.15050734000704.17451046289722.15951048386864.1625129529166.163 51683311886.16351816630506.14951816630506.15051976612822.18251978710002.19752523015482.15952567164907.14952567164907.15052567164907.16352567164907.17952569147371.17252579502455.17252579502455.17352682867945.14952682867945.15052736796155.5  53322291235.19253386120174.17953493744851.16854224864146.17054404701703.17254959380579.19255473260884.14855989238223.17256102654486.17756115695737.19756117792861.18256170256219.17256170498639.15156956174629.15257022093363.17057122396082.19757124493206.18257261298738.19757263395862.1825750404535.182 58080061534.14958080061534.15058152725582.16358174797435.16358369446314.16958730541225.18258732638349.19758840920286.16358987689625.17958998195513.16359314873579.14759314873579.14959314873579.15159338331354.16359586081466.17760385159294.17960795071034.16261482382924.15161671386902.15861673380011.5  61855565731.19261884732010.16961937685145.15961939782289.16161939782290.1806201887545.152 62299570606.1636298254074.179 63826654415.17263999581114.2  64026414714.16364738246334.16364897170030.16864897170030.18364996132282.16265128844401.17065164961555.19265204828578.16166028155702.15566028155702.17366070830614.18766330498723.16067180176575.5  67469470029.15567469470029.44 67924670142.14967924670142.15067943285742.17968037925795.19268398178269.17068591795262.14968591795262.150721185103.172  8116721570.160 8646118925.1   00000>00Q00R00Y00b00c00d01201301A01O01P01^01l02:02;02<02=02>02?02]02^02_02m03;03<03J03N03_03`03a03b04O05305705805V06406E06V06W07L07Z07[09?0:f0:l0;20;@0;N0;O0;P0;Q0;V0;[0;`0;a0;b0;g0<A0<O0<]0<^0<b0=C0=d0>E0>K0>`0>a0>d0?20?30?X0@J0@Q0@R0@W0A50A60A70A80AQ0AR0AS0AT0AU0AV0AW0AZ0A]0A^0B10B20BI0B`0Ba0CB0Co0D=0DP0DQ0DR0DS0E40EU0EV0F40FR0Fg0Fk0Fl0G10G50G90GI0Gg0H50HC0HD0HW0HX0HY0HZ0H[0H\0I90II0Ij0J40JU0Jc0Jd0Je0K60KG0Ka0Ko0L40LE0LV0LW0LX0Li0M:0M;0MI0MJ0MK0ML0MP0MU0Mc0N<0N=0O00Oc0Od0Oe0Of0PC0P`0Pa0Pb0Pc0Q30Q40QI0Qg0R50RO0Ri0S@0SA0SB0SP0ST0SX0S\0Sm0T>0T?0T@0TA0TB0TC0V50VP0VQ0Vj0WC0WD0WY0Wg0Wl0XU0XV0Xk0YB0YU0YZ0Z00ZF0ZK0ZL0ZP0ZQ0Zb0[30[D0[U0[Z0[h0\60\D0\E0\W0\f0]50]R0]k0^D0^M0^\0^o0_30_40_Q0_R0_S0_W0_X0_m0``0a20aD0aV0bC0bQ0bk0c>0c?0cC0c`0d10dB0dC0dH0da0db0e10e@0eA0eE0eF0fD0gN0g\0gj0h80hM0i>0iL0iZ0im0in0ioS3HUB4ABLO3RZRS4CEIL2LO2N02R03HspSS2N12R1S3SZB3LTBSSS3HUB4ABLO3RZRFS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRFSSSFS3HUB4ABLO3HPG3SB23SB33SB43RZRSFS3HUB4ABLO3RZRS3HUB4ABLO3RZRFS3HUB4ABLO3RZRS2HBS4CEIL2LO3CX13HspSFSS1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RZR3RLR3RSR2K21HS1N3HUB4ABLO4UBHI3NSZ2NS3RZR3RSR3NSRS2HBFS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3FS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RLR3RSR3RSM2K02K32K4S3HUB4ABLO3RZRFS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RLR3RSR3RSM3NSR2K02K32NE4SHN04SHS01HS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RLR3RSR3RSM3NSR2K02K32K42NE4SHN04SHS01HS4CEILS4CEILS3HUB4ABLO3RZRS3HUB4ABLO3RZRSFSS3HPGS3HPGS3S47FFS3HspS3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRFS2B1S1N3HUB4ABLO4AB163LTB3RZR3RZE3RLRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLRS4UB16S4CEIL2LO3SB13SB23HspSS1NS3HUB4ABLO3RZRSS4CEIL2LO3HPG3SB23SB33SB43Hsp3LTB3SPSS4CEIL2LO3HUB4ABLO4UBHI3NSZ3HPG3SB42NS3RZR3RSR3HspS2N02R0SS3SPSS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRFFFS4CEIL2LO3HPG3SB43SPS3HspSSSSSSS1NS1NSS4CEIL2LO2N02R03HspSS3HUB4ABLO4UBHI3NSZ3NSRS3HUB4ABLO4UBHI3NSZ3NSRSS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RLR2K02K32DXS3HUB4ABLO3RZRS4CEIL2LO2N02R03HspSFSS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRFS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3HPG3SB23SB33SB43RZRS4CEIL2LO3SB13SB23HspS2LOSS3HspS2HBS2HBS4CEIL2LO2T13HspS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS4CEIL2LO2N02R03HspSSSFSS1N4ABLO2T02T13LTB3RZR3RLR2K0S2NS3RZR3RSR3NSRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS4AB163RZMS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS3HUB4ABLO3RZRFFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3RZRS3HspS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3FFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3FS3HUB4ABLO3RZRSSSS2HBS3HspS3HUB4ABLO3RZRS4CEIL2LO4UBHI3NSZ2NS3RSRSS3HUB4ABLO3SB44PW013RZR3HPG3SB33SB24CEIL2LO3LTB3SPSS3HPG3SB33HUB4ABLO3SB44PW013RZR3SB24CEIL2LO3LTB3SPSSSSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRSSSS2NS3RZR3RSR3NSRFS4CEIL2LO3SB13SB23HspS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO3SPS2N12R13HspSSS3HUB4ABLO3RZRS2HBS2HBS2HBS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3SSSSSS4CEIL2LO1N3HUB4ABLO4UBHI4AB163NSZ2T03LTB2N12R12NS3RZR3RZE3RLR3RSR2K02K32X12X21H3HPG3SB13SB23SB33SB44SHN04SHS03RSMS4CEIL2LO2N12R13Hsp3LTB3SPSFS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRFS4CEIL2LO3SB13SB23HspS3HUB4ABLO3RZRS3IDRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLR3RSR3RSMFS4CEIL2LO3SB13SB23HspS3HUB4ABLO4UBHI3NSZ3NSRS4CEIL2LO2N02R03HspS3IDRS4CEIL2LO3SB43SPS4PW01S4CEIL2LO3SB43SPS4PW01S3HspSS2LOSS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3IDRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS1N2NS3RZR3RSR3NSRS4CEIL3SB44PW01S4CEIL3SB44PW01S4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS4ABLO2K0S3HUB2NS3RSR2K2S4ABLO2T03LTB2K02K3S2HBSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRSSS2B1FS4CEIL2LO3SB13SB23HspS1N3HUB4ABLO4AB163LTB2NS3RZR3RZE3RLR3RSR3RSM3NSR2K2S1N2NS3RZR3RSR3NSRS1N2NS3RZR3RSR3NSRS1N2NS3RZR3RSR3NSRS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RLR2K02K32DXS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO2N02R03HspFS2HBS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4UBHI3NSZ2NS3RSRS4UBHI3NSZ2NS3RSRSS3SB3S4CEIL2LO3HPG3SB33SB43HspSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HSS2LOFS1N3HUB4ABLO4AB162T03LTB2NS3RZR3RZE3RLR3RSM3NSR2K02K32Ha2X12X2S4CEIL2LO2N12R12Ha1H3HUB4ABLO3RZR2X12X24SHN04SHS03HPG3SB13SB23SB43SB34PW01S3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS4CEIL2LO3SB13SB23HspS1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RZR3RLR3RSR3NSR2K21HS3HUB4ABLO3RZRS3HUB4ABLO3RZRS4CEIL2LO2N02R03HspSS".
assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  assert (UB16 : UB mod 16 = 0).
  { rewrite HUB. clear -AB16 RZM. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  word_range sp SPR.
  destruct PC as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7).
  pose proof (munch_refl (allocBC_WG L sp UB PG pgw n) m) as MU. pose proof (wmono_refl bsegs m) as WM.
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
  2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. clear -UB16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
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
      assert (SHP' : n mod 8 <> 0 -> rw_cells bsegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0x99000 _ => exact PC1
         | |- rw_cells _ _ 0xa1038 _ => exact PC4
         | |- rw_cells _ _ 0xa1d20 _ => exact PC5
         | |- rw_cells _ _ 0xa089c _ => exact PC6
         | |- rw_cells _ _ 0x9e88d _ => exact PP
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
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
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
      assert (SHP' : n mod 8 <> 0 -> rw_cells bsegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0x99000 _ => exact PC1
         | |- rw_cells _ _ 0xa1038 _ => exact PC4
         | |- rw_cells _ _ 0xa1d20 _ => exact PC5
         | |- rw_cells _ _ 0xa089c _ => exact PC6
         | |- rw_cells _ _ 0x9e88d _ => exact PP
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
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithDepot.
End CANSEC1.
