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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AModelFacts F_memset F_apoison F_aalloc_s.
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
             F (Z_to_bv 64 0x3177c) fc None m' (seg_rom bsegs)
    /\ munch (allocBC_W L sp UB PG pgw n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 (hdr_b1_mid b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

(* [comment removed for export] *)
#[using="Type"] Lemma partial_spec : forall RNG (n UB PG pgw : Z) (pj : byte) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  mem_inv bsegs m ->
  1 <= n <= 448 -> PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
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
  assert (SHR : 0x7fff8000 <= shad UB /\ 0 <= shlen (n - n mod 8) <= 56 /\ PG + 1 <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF in *. Local Ltac2 Set LiaHints.tbl := fun () => "00f0>11383758314.6911385855457.7316630097935.6023495003441.5823495003830.6127238478433.5928277756440.5928277756440.6228913119921.7028915217076.6628915217081.7229782367974.5729784416474.6129784417117.5830784453914.5830784454301.6133858871586.5933858871586.6234969967195.5934969967195.6235810301874.573664093147.70 3664093147.74 47552575323.5947552575323.6252076332701.6853649105243.5953649105243.6255019083177.7055019083177.7455148979235.6055148979362.6155148980005.5855148980132.5955157802157.6955157802157.7259308548964.6059308628433.5959308628566.6059308628695.6159588178609.7060802846458.5761884731502.5961929812114.5961929812241.5861929812630.6161937685146.6861939782289.74703684731.59  703684731.62  8010146619.59 8010146619.62 9393672027.59 9393672027.62 00000100200?00@00A00L00P00T00U00V00W00X00Y00Z00g01201301401=01F01G01H01I01R01[01\01e01n01o02002702>02T02a03303:03H03U03b04704804O04R04U04X04[04^04a04j05305805=05F05OSSS1N4UBLO2K01eSSS1N4UBLO2K0S2HBS2HBSSSSSSS1N3UB82K02K1S3UB82K02K4SSS3HPG3SHRS3HPG3SHRSSSS3HPG3SHRS3HPG3SHRFS3HPG3SHRS3HPG3SHRSSS2K12K2S2K12K2S1N4UBLO4UBHI3UB81H2K0S1N4UBHI1H2K1S1N4UBLO3UB82K02K1S2K12K2S1N4UBLO2K02NES1N4UBHI1H2K2S1N4UBHI1H2K3S1N4UBLO3UB82K02K12K4SS1N3HPG4UBLO4UBHI3UB81HS1NS1NS1NS1NS1NS1NS3HPG3SHRS3HPG3SHRS3SHRS3SHRS3HPG3SHRS3HPG3SHR".
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
  stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv bsegs m ->
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
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->       (* [comment removed for export] *)
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
  evtF bsegs RNG (allocBC_post L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
    (MS (mkR (Z_to_bv 64 0x314d0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x314d0) fc None m (seg_rom bsegs)).
Proof.
  intros until s11v.
  intros ST CEIL LO MI TP N HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
         SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.   (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "04;0?10054784078.16110194000543.17010313444268.4  1047820382.150 10625553216.15010669833637.17410721241625.16110842551374.16111191675278.2  11480366910.14711480366910.14811752483811.12211925506990.16112270362430.14712270362430.14812428150072.18912480772618.1671324746171.158 1324746171.161 13313577562.3  13336768858.16113367089074.1761343986644.170 13923957822.14713923957822.14814014474241.4  14159447534.17714311754318.17715319906838.17115830019643.16115948676913.4  16346643763.17516486372681.16816512576796.14616528622318.16116545774130.5  16557567661.16616557567661.18116594262294.18016596359474.19516963689266.3  1728976368.168 17601143726.16117833946714.3  17949008832.17117949008832.18617986879152.15017986879152.16818365406014.14718365406014.14818430975599.15919117323662.2  19352503472.16119517033132.16619517033132.18119682054918.1501990225994.3   20158040118.17520322563816.3  20719413306.16120857720078.17721062356398.16121195996626.14721969407398.14722718042091.16622718042091.16822718042091.18123891548451.19024211191904.4  2431248216.147 24892159950.16124982578737.14525076071819.18925076071819.19025157604214.1502597469155.175 25996042971.15026403658112.15827028261662.4  27775112880.4  27943014742.4  28040491972.19028242461078.16828485987241.16028656514152.4  28729582384.5  29021953738.3  29782367974.14629782367974.16730047027402.3  301011343.170  30430348547.15630507154306.14430517090690.17830613629521.14931192993456.16131366954517.15031498178222.16131791172943.17032475639163.17732769400735.16632769400735.18132932373168.4  33082065689.17733262659552.14733262659552.14833445853437.2  33577178314.14733577178314.14833764744995.19033875467557.1683392152800.157 34028498699.3  34170950174.14734170950174.14834243631625.17234755885818.17734779080494.1613495373902.161 35289778563.15935711452879.17036254216601.15736254216601.15836254216601.16136376561033.4  36534319948.4  36635088727.14836702058843.14736967174608.16139523213398.4  39896594704.17740194010222.17740858487054.4  41030367075.17241647040034.19541649137158.18041792303450.16141843714542.177423940875.3    42614983602.19542617080726.18042677208786.14742805740039.18943706322738.19543708419862.18043990206109.4  44052358222.16144820102307.14744820102307.14844820102307.16145221239098.17745480795915.3  4565746606.161 45699881561.1614573656713.2   45891680928.18045893778052.19546298861963.15846988300803.12247039319577.16147244432302.14747244432302.14848240491802.16048242588945.15648242588946.15748738442331.14748865763193.2  49133638259.19049181239354.1615012112366.177 50645046474.14750645046474.14850734000704.17251046289722.15751048386864.1605129529166.161 51683311886.16151816630506.14751816630506.14851976612822.18051978710002.19552523015482.15752567164907.14752567164907.14852567164907.16152567164907.17752569147371.17052579502455.17052579502455.17152682867945.14752682867945.14852736796155.5  53322291235.19053386120174.17753493744851.16654224864146.16854404701703.17054959380579.19055473260884.14655989238223.17056102654486.17556115695737.19556117792861.18056170256219.17056170498639.14956956174629.15057022093363.16857122396082.19557124493206.18057261298738.19557263395862.1805750404535.180 58080061534.14758080061534.14858152725582.16158174797435.16158369446314.16758730541225.18058732638349.19558840920286.16158987689625.17758998195513.16159314873579.14559314873579.14759314873579.14959338331354.16159586081466.17560385159294.17760795071034.16061482382924.14961671386902.15661673380011.5  61855565731.19061884732010.16761937685145.15761939782289.15961939782290.1786201887545.150 62299570606.1616298254074.177 63826654415.17063999581114.2  64026414714.16164738246334.16164897170030.16664897170030.18164996132282.16065128844401.16865164961555.19065204828578.15966028155702.15366028155702.17166070830614.18566330498723.15867180176575.5  67469470029.15367469470029.44 67924670142.14767924670142.14867943285742.17768037925795.19068398178269.16868591795262.14768591795262.148721185103.170  8116721570.158 8646118925.1   00000>00Q00R00Y00b00c00d01201301A01O01P01^01l02:02;02<02=02>02?02]02^02_02m03;03<03J03N03_03`03a03b04G04k04o05005N05l06=06N06O07@07N07O0920:U0:[0:a0:o0;=0;>0;?0;@0;E0;J0;O0;P0;Q0;V0<00<>0<L0<M0<Q0<n0=K0=h0>=0>>0>A0>O0>P0?50?g0?n0?o0@40@R0@S0@T0@U0@n0@o0A00A60A70A80A90A:0A;0AN0AO0Af0B=0B>0B_0CH0CV0Ci0Cj0Cm0D00D10D20DS0E40E50ES0F10FF0FJ0FK0FP0FT0FX0Fh0GF0GT0Gb0Gc0H60H70H80H90H:0H;0HP0HS0I40I<0I]0Ik0Il0Im0J>0JO0Ji0K70K<0KM0K^0K_0K`0L10LB0LC0LQ0LR0LS0LT0LX0L]0Lk0MD0ME0N80Nk0Nl0Nm0Nn0OK0Oh0Oi0Oj0Ok0On0Oo0PD0Pb0Q00QJ0Qd0R;0R<0R=0RK0RO0RS0RW0Rh0S90S:0S;0S<0S=0S>0Tl0UG0UH0Ua0V:0V;0VP0V^0Vc0WH0WI0W^0X50XH0XM0Xc0Y90Y>0Y?0YC0YD0YU0Yf0Z70ZH0ZM0Z[0Zi0[70[80[;0[J0[Y0\60\O0\h0]10]@0]S0]W0]X0^50^60^70^;0^<0^Q0_@0_C0_F0_I0`20`@0`Z0`m0`n0a20aO0a`0b10b20b70bP0bQ0b`0bo0c00c40c50co0e90eG0eU0ec0f80fe0g30gA0gT0gU0gVS3HUB4ABLO3RZRS4CEIL2LO2N02R03HspSS2N12R1S3SZB3LTBSSS3HUB4ABLO3RZRFS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRFSSSFS3HUB4ABLO3HPG3SB23SB33SB43RZRSFS3HUB4ABLO3RZRS3HUB4ABLO3RZRFS3HUB4ABLO3RZRS2HBS4CEIL2LO3CX13HspSFSS1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RSR2K21HS1N3HUB4ABLO4UBHI3NSZ2NS3RZR3RSR3NSRS2HBFS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3FS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RSR3RSM2K02K32K4S3HUB4ABLO3RZRFS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RSR3RSM3NSR2K02K32K42NE4SHN04SHS01HS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RSR3RSM3NSR2K02K32K42NE4SHN04SHS01HS4CEILS4CEILS3HUB4ABLO3RZRS3HUB4ABLO3RZRSFSS3HPGS3HPGS3S47FFS3HspS3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRFS2B1S1N3HUB4ABLO4AB163LTB3RZR3RZES1N3HUB4ABLO4AB163LTB3RZR3RZES1N3HUB4ABLO4AB163LTB3RZR3RZES4CEIL2LO3SB13SB23HspSS1NS3HUB4ABLO3RZRSS4CEIL2LO3HPG3SB23SB33SB43Hsp3LTB3SPSS4CEIL2LO3HUB4ABLO4UBHI3NSZ3HPG3SB42NS3RZR3RSR3HspS2N02R0SS3SPSS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRFFFS4CEIL2LO3HPG3SB43SPS3HspSSS4AB16SSSSSS4CEIL2LO2N02R03HspSS3HUB4ABLO4UBHI3NSZ3NSRS3HUB4ABLO4UBHI3NSZ3NSRSS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS1N3HUB4ABLO4AB162T03LTB3RZR3RZE2K02K32DXS3HUB4ABLO3RZRS4CEIL2LO2N02R03HspSS1NS1NFSS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRFS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3HPG3SB23SB33SB43RZRS4CEIL2LO3SB13SB23HspS2LOSS3HspS2HBS2HBS4CEIL2LO2T13HspS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS4CEIL2LO2N02R03HspSSSFSS1N4ABLO2T02T13LTB2K0S1NS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS4AB161HS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS3HUB4ABLO3RZRFFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3RZRS3HspS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3FFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3FS3HUB4ABLO3RZRSSSS2HBS3HspS3HUB4ABLO3RZRS4CEIL2LO4UBHI3NSZ2NS3RSRSS3HUB4ABLO3SB44PW013RZR3HPG3SB33SB24CEIL2LO3LTB3SPSS3HPG3SB33HUB4ABLO3SB44PW013RZR3SB24CEIL2LO3LTB3SPSSSSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRSSSS1NFS4CEIL2LO3SB13SB23HspS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO3SPS2N12R13HspSSS3HUB4ABLO3RZRS2HBS2HBS2HBS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3SSSSSS4CEIL2LO1N3HUB4ABLO4UBHI4AB163NSZ2T03LTB2N12R12NS3RZR3RZE3RSR2K02K32X12X21H3HPG3SB13SB23SB33SB44SHN04SHS03RSMS4CEIL2LO2N12R13Hsp3LTB3SPSFS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRFS4CEIL2LO3SB13SB23HspS3HUB4ABLO3RZRS3IDRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RSR3RSMFS4CEIL2LO3SB13SB23HspS3HUB4ABLO4UBHI3NSZ3NSRS4CEIL2LO2N02R03HspS3IDRS4CEIL2LO3SB43SPS4PW01S4CEIL2LO3SB43SPS4PW01S3HspSS2LOSS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3IDRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS1NS4CEIL3SB44PW01S4CEIL3SB44PW01S4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS4ABLO2K0S3HUB2NS3RSR2K2S4ABLO2T03LTB2K02K3S2HBSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRSSS2B1FS4CEIL2LO3SB13SB23HspS1N3HUB4ABLO4AB163LTB2NS3RZR3RZE3RSR3RSM3NSR2K2S1NS1NS1NS1N3HUB4ABLO4AB162T03LTB3RZR3RZE2K02K32DXS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO2N02R03HspFS2HBS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4UBHI3NSZ2NS3RSRS4UBHI3NSZ2NS3RSRSS3SB3S4CEIL2LO3HPG3SB33SB43HspSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HSS2LOFS1N3HUB4ABLO4AB162T03LTB2NS3RZR3RZE3RSM3NSR2K02K32Ha2X12X2S4CEIL2LO2N12R12Ha1H3HUB4ABLO3RZR2X12X24SHN04SHS03HPG3SB13SB23SB43SB34PW01S3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS4CEIL2LO3SB13SB23HspS1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RZR3RSR3NSR2K21HS3HUB4ABLO3RZRS3HUB4ABLO3RZRS4CEIL2LO2N02R03HspSS".
assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (UB16 : UB mod 16 = 0).
  { rewrite HUB. pose proof (rz_size_small_cases n N). clear -AB16 H. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  word_range sp SPR.
  destruct PC as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7).
  pose proof (munch_refl (allocBC_W L sp UB PG pgw n) m) as MU. pose proof (wmono_refl bsegs m) as WM.
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
      assert (SHP' : n mod 8 <> 0 -> rw_cells bsegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_spec RNG n UB PG pgw pj).
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
      assert (SHP' : n mod 8 <> 0 -> rw_cells bsegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_spec RNG n UB PG pgw pj).
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
    apply evtF_done. unfold allocBC_post. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithDepot.
End CANSEC1.
