(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase ADepot_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2 AModelFacts APrimFacts F_memset F_apoison F_aalloc_s.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac band_lin :=
repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
Section CANSEC1. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.
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
F (Z_to_bv 64 0x328d4) fc None m' (seg_rom bsegs)
/\ munch (allocBC_WG L sp UB PG pgw n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp + -128)
/\ 0 < id < 2^31
/\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 (hdr_b1_mid b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
/\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
/\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
/\ ADEPOT DI L m'.
#[using="Type"] Lemma partial_specG : forall RNG (n UB PG pgw : Z) (pj : byte) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem),
mem_inv bsegs m ->
1 <= n -> PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
ablk UB (UB + n) -> UB + n <= ATOP -> UB mod 8 = 0 ->
rw_cells bsegs m 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)] ->
rw_cells bsegs m 0xa2538 [C8 (Z_to_bv 64 0x7fff8000)] ->
rw_cells bsegs m 0xa3220 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m 0xa1d9c [C1 (Z_to_bv 8 1)] ->
rw_cells bsegs m 0x9fd8d [C1 (Z_to_bv 8 1)] ->
(n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->
rng_aimg RNG -> (n mod 8 <> 0 -> rng RNG PG 1) ->
evtF bsegs RNG (fun ms' => exists ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' m',
ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 UB) s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x328d4) fc None m' (seg_rom bsegs)
/\ munch [(PG, PG + pgw)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))]))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 UB) s5 (Z_to_bv 64 (n - n mod 8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32840) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros MI N HPG HPW UBLO UBHI UB8 GOT SHB LAY CANP PP SHP RIMG RPG.
pose proof (munch_refl [(PG, PG + pgw)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
unfold ablk, AIMG_HI, KLS in UBLO. atop_facts.
assert (SHR : 0x7fff8000 <= shad UB /\ 0 <= shlen (n - n mod 8) /\ PG + 1 <= 0x10007fff8000).
{ unfold shad, shlen, ASHOFF in *. Local Ltac2 Set LiaHints.tbl := fun () => "00f0>11383758314.6911385855457.7312965018203.5912965018203.6216630097935.6023495003441.5823495003830.6123716442459.5923716442459.6227238478433.5928277756440.5928277756440.6228913119921.7028915217076.6628915217081.7229782367974.5729784416474.6129784417117.5833310381659.5933310381659.6233858871586.5933858871586.623664093147.70 3664093147.74 52076332701.6855019083177.7055019083177.7455148979235.6055148979362.6155148980005.5855148980132.5955157802157.6955157802157.7259308548964.6059308628433.5959308628566.6059308628695.6159588178609.7059663788513.9359663788513.9661884731502.5961929812114.5961929812241.5861929812630.6161937685146.6861939782289.7465692549243.5965692549243.627262431154.57 8010146619.59 8010146619.62 8443034364.78 9877602139.59 9877602139.62 00000100200;00D00Q00R00S00\00e01001401801901:01;01<01=01>01G01P01Q01R01S01T01U01V01W01^01e02;02H02Z02a02o03<03I03^03_04L05705F05U05g06906K06]06f06o07007507:07b07k084SSS3HPG3SHRS3HPG3SHRS1N4UBLO2K01eSSS3HPG3SHRS3HPG3SHRS1N4UBLO2K0S2HBS2HBSSSSSSS3HPG3SHRS3HPG3SHRSSSSFSSS2K12K2S2K12K2S1N4UBLO4UBHI3UB81H2K0S1N4UBHI1H2K1S1N4UBLO3UB82K02K1S2K12K2S1N4UBLO2K02NES1N4UBHI1H2K2S1N4UBHI1H2K3S1N4UBLO3UB82K02K12K4SS1N3UB82K02K12H02H12H52H63H103H113H153H163H20S3UB82K02K42H02H12H52H63H103H113H153H163H20S1N4UBLO4UBHI1HS1N4UBLO4UBHI1HS1N4UBLO4UBHI1H2K0S1N4UBLO4UBHI1H2K0S1N4UBLO4UBHI1H2K0S1N4UBLO4UBHI1H2K0S3HPG3SHRS3HPG3SHRSS3SHRS3SHRS1N3HPG4UBLO4UBHI3UB81H2H02H52H63H103H11S3HPG3SHRS3HPG3SHR".
rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. Z.div_mod_to_equations. lia. }
step. if_cases K0; zify_cond K0.
{ apply evtF_done. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. intros NE. exfalso. lia. }
specialize (SHP ltac:(lia)). specialize (RPG ltac:(lia)).
assert (PW1 : pgw = 1) by (rewrite HPW; destruct (Z.eqb_spec (n mod 8) 0); [lia|reflexivity]). clear HPW. subst pgw.
step. callp can_poison_spec; [exact CANP|]. step. if_lit.
step. step. step.
zstep. zstep. zstep. zstep. zstep.
change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
step. if_cases K1; zify_cond K1.
2: step; step; step; step; step; step; zstep.
2: step; if_cases K2; zify_cond K2; [| exfalso; lia].
2: step; step; step; zstep; zstep.
2: step; if_cases K3; zify_cond K3; [exfalso; lia|].
2: step; if_cases K4; zify_cond K4; [exfalso; lia|].
all: step; step; lstep; zstep; zstep.
all: setreg 10 (Z_to_bv 64 PG) ltac:(rewrite HPG; unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; f_equal; Z.div_mod_to_equations; lia).
all: zstep; zstep; zstep.
all: rewrite (land_ones_r n) by lia; change 7 with (2^3 - 1) at 1; rewrite (zb_land_mask n 3) by lia; change (2^3) with 8.
all: sstep.
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
UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
(t + 4096 <= AB \/ AB + 65536 <= t) -> sclr t 4096 ->
(al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) -> sclr (al_ctx L) 65536 ->
(al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> sclr (al_nodes L) 1048576 ->
(al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> sclr (al_store L) 8388608 ->
0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
rw_cells bsegs m (bv_unsigned sp + -128)
[CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
0 <= b1 < 256 ->
rw_cells bsegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sj] ->
(n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->
poison_cells m -> rw_cells bsegs m 0x9fd8d [C1 (Z_to_bv 8 1)] ->
rw_cells bsegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
u64arr bsegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
ADEPOT DI L m ->
AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
rng RNG (UB - 16) 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
evtF bsegs RNG (allocBC_postG L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
(MS (mkR (Z_to_bv 64 0x32628) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
(Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
(Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
t3 t4 t5 t6)
F (Z_to_bv 64 0x32628) fc None m (seg_rom bsegs)).
Proof.
intros until s11v.
intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.
Local Ltac2 Set LiaHints.tbl := fun () => "04D0?10122409774.16310313444268.4  1047820382.152 10625553216.15210669833637.17610721241625.16310975380398.16311191675278.2  11752483811.12312131124654.16312136140899.19212256220118.18212258317298.19712428150072.19112480772618.1691324746171.160 1324746171.163 13313577562.3  13336768858.16313367089074.1781343986644.172 14311754318.17915210431638.18215212528818.19715319906838.17315795316387.19215830019643.16315948676913.4  1632403378.197 1634500502.182 16346643763.17716486372681.17016512576796.14816528622318.16316545774130.5  16557567661.16816557567661.18316748370326.18216750467506.1971728976368.170 17833946714.3  17949008832.17317949008832.18817986879152.15217986879152.17018430975599.16118897660303.17218919718986.3  19117323662.2  1927196194.197 1929293318.182 19352503472.16319517033132.16819517033132.18319682054918.15220158040118.17720322563816.3  20670856254.14920670856254.15020719413306.16321195996626.14921969407398.14922168096458.3  22294345678.16322718042091.16822718042091.17022718042091.18323036111982.17924211191904.4  2431248216.149 24982578737.14725076071819.19125076071819.19225157604214.15225381061550.16325792348067.1922597469155.177 25996042971.15226403658112.16027335527918.17927775112880.4  27943014742.4  28040491972.19228485987241.16228696517455.17228729582384.5  28790624927.17229782367974.14829782367974.16929965292900.16829965292900.18330430348547.15830507154306.14630517090690.18030613629521.15131192993456.16331281687630.16331366954517.15231913181519.1723193401494.182 3195498674.197 32008254371.19232475639163.17932716547054.17932932373168.4  33082065689.17933262659552.14933262659552.15033415002206.14933415002206.15033445853437.2  33577178314.14933577178314.15033875467557.1703392152800.159 34022839870.14934022839870.15034028498699.3  34170950174.14934170950174.15034243631625.17434722495550.14934722495550.15034755885818.17935289778563.16135310472686.17936254216601.15936254216601.16036254216601.16336376561033.4  3645019214.163 36534319948.4  36635088727.15036702058843.14936967174608.16336979723342.16337751427478.17038404006830.16339180720958.14939180720958.15039750081615.17239896594704.17940059657198.17941030367075.17441072247790.17941792303450.16341861025198.163423940875.3    42677208786.14942805740039.19144277085886.14944277085886.15044329598222.17944820102307.14944820102307.15044820102307.16345221239098.17945243883939.19245335424078.16345480795915.3  45699881561.1634573656713.2   45891680928.18245893778052.19746298861963.16046807179466.3  46988300803.12347039319577.16347039468566.18747244432302.14947244432302.15047420759102.14947420759102.15048240491802.16248242588945.15848242588946.15948289525761.4  48738442331.14948865763193.2  49181239354.16350199324494.16350645046474.14950645046474.15050734000704.17451046289722.15951048386864.16251408114482.3  51683311886.16351816630506.14951816630506.15052523015482.15952567164907.14952567164907.15052567164907.16352567164907.17952569147371.17252579502455.17252579502455.17352682867945.14952682867945.15052736796155.5  53493744851.16854224864146.17054404701703.17255473260884.14855877473202.19755879570326.18256007886318.17956102654486.17756115695737.19756117792861.18256170256219.17256170498639.15156177073230.16356563527971.19256956174629.15256968812338.19756970909462.18257022093363.17057054875198.14957054875198.1505750404535.182 58174797435.16358369446314.16958730541225.18258732638349.19758840920286.16358987689625.17958998195513.16359314873579.14759314873579.14959314873579.15159338331354.16359586081466.17760385159294.1796079053230.163 60795071034.16261320090398.4  61482382924.15161671386902.15861673380011.5  61884732010.16961937685145.15961939782289.16161939782290.1806201887545.152 6234796707.192 6298254074.179 62987396431.1726309898867.192 63999581114.2  64026414714.16364162503758.16364738246334.16364897170030.16864897170030.18364996132282.16265128844401.17065164961555.19265204828578.16166028155702.15566028155702.17366149329551.25 66151427842.16 66330498723.16066920267471.17267180176575.5  67469470029.15567469470029.44 6831021742.163 68398178269.1707460339982.4   8116721570.160 8419811407.172 8646118925.1   9715187357.4   00000>00?00F00O00P00Q00_00`00a00o01D01U01f01g01h01i01j01k02I02J02K02O02`03103B03W03X03Y03j04;04<04i05M05Q05R06006N06_07007e07f09J0;10;70;=0;>0;Q0;R0;S0;d0<50<60<;0<@0<E0<F0<K0<Y0<g0=A0=B0=F0=G0=U0>60>W0?80?F0?G0?J0?K0@00@b0@i0A70AL0AM0AR0B00B>0B?0B@0BY0BZ0Bm0Bn0CA0CB0CC0CF0CI0CJ0Ca0D80D90DZ0Dh0EU0Eh0F90FJ0F_0F`0Fn0Fo0G00GQ0H20H@0HN0HO0Hm0IK0IO0IP0I^0Il0J10J50J90JI0JW0Je0KC0KD0KR0KS0KT0KU0KV0Kd0Ke0LB0LR0M30MA0MB0MP0M^0Ml0N?0N`0Nn0No0O=0OW0Oe0Oj0Ok0Ol0P:0PH0PV0PW0PX0PY0P]0Q20Q@0QE0Q^0Q_0RR0SE0SF0SG0SH0SI0SJ0Sg0TD0TR0T`0Ta0Tb0Tc0Td0U40U50US0Ua0V;0VU0Vl0Vm0Vn0Vo0W30W70W;0W<0W=0W>0W?0W@0Y20YM0YN0Yg0Z@0ZA0ZF0Zo0[00[G0[X0[i0\70\<0\R0\h0\m0\n0]<0]Q0]U0]f0^70^80^F0^T0^Y0^Z0^l0_;0_J0_g0`@0`Y0`b0a10aD0aH0aI0af0b40b50b60b70b;0b<0bo0cA0cS0ce0dR0dg0eA0eT0ei0ej0en0f<0fY0fj0g;0g<0gA0gZ0g[0gj0h90hN0h\0h`0i30i40j20k<0kJ0l;0l<0l=0lP0lQ0lRS3HUB4ABLO3RZRSS2N12R1S3SZB3LTBSSS3HUB4ABLO3RZRFSS3HUB4ABLO3RZRS4CEIL2LO3SB13SB23HspS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3FSSSFS3HUB4ABLO3HPG3SB23SB33SB43RZRSFS2HBS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S4CEIL2LO3CX13HspS4CEIL2LO3SB13SB23HspSFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3SS1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RZR3RLR3RSR2K21HS1N3HUB4ABLO4UBHI3NSZ2NS3RZR3RSR3NSRS2HBFS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RLR3RSR3RSM2K02K32K4FS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RLR3RSR3RSM3NSR2K02K32NE4SHN04SHS01HS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RLR3RSR3RSM3NSR2K02K32K42NE4SHN04SHS01HS4CEILS4CEILSS4CEIL2LO2N02R03HspFFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3SS3HPGS3HPGS3S47FS3HspS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRFS2B1SS3HUB4ABLO3RZRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLRS3HUB4ABLO3RZRSS1NSS4CEIL2LO3HPG3SB23SB33SB43Hsp3LTB3SPSS4CEIL2LO3HUB4ABLO4UBHI3NSZ3HPG3SB42NS3RZR3RSR3HspS2N02R0S3HUB4ABLO3RZRS4CEIL2LO3SB13SB23HspSS3SPSS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HUB4ABLO3RZRFFS4CEIL2LO3HPG3SB43SPS3HspSS4CEIL2LO2N02R03HspSS4CEIL2LO2N02R03HspSSS1NS1NSS3HUB4ABLO4UBHI3NSZ3NSRS3HUB4ABLO4UBHI3NSZ3NSRSS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS3HUB4ABLO3RZRS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RLR2K02K32DXS4CEIL2LO2N02R03HspS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S4CEIL2LO3SB13SB23HspSS3HUB4ABLO3RZRFSS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS3HUB4ABLO3RZRS3HUB4ABLO3RZRFS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3HPG3SB23SB33SB43RZRS2LOSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HspS2HBS2HBS4CEIL2LO2T13HspS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB23SB33SB43RZRSS3HUB4ABLO3RZRSSSFS3HUB4ABLO3RZRSS1N4ABLO2T02T13LTB3RZR3RLR2K0S2NS3RZR3RSR3NSRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS3HUB4ABLO3RZRSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS4CEIL2LO2N02R03HspS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS3HUB4ABLO3RZRFS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3RZRS3HspFFS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRSSSS2HBS4CEIL2LO3SB13SB23HspS3HUB4ABLO3RZRS3HspS4CEIL2LO4UBHI3NSZ2NS3RSRSS3HUB4ABLO3SB44PW013RZR3HPG3SB33SB24CEIL2LO3LTB3SPSS3HPG3SB33HUB4ABLO3SB44PW013RZR3SB24CEIL2LO3LTB3SPSSSSSSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS3HUB4ABLO3RZRS3HUB4ABLO3RZRSSSFS2NS3RZR3RSR3NSRFS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO3SPS2N12R13HspSSFS2HBS2HBS2HBSSSSSS4CEIL2LO1N3HUB4ABLO4UBHI4AB163NSZ2T03LTB2N12R12NS3RZR3RZE3RLR3RSR2K02K32X12X21H3HPG3SB13SB23SB33SB44SHN04SHS03RSMS4CEIL2LO2N12R13Hsp3LTB3SPSFS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRFS3IDRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLR3RSR3RSMFS3HUB4ABLO4UBHI3NSZ3NSRS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HUB4ABLO3RZRS3IDRS4CEIL2LO3SB43SPS4PW01S4CEIL2LO3SB43SPS4PW01S3HspSS3HUB4ABLO3RZRS4CEIL2LO3SB13SB23HspS2LOS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3SS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3IDRSS1N2NS3RZR3RSR3NSRS4CEIL3SB44PW01S4CEIL3SB44PW01S4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS4ABLO2K0S3HUB2NS3RSR2K2S4ABLO2T03LTB2K02K3S2HBSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS3HUB4ABLO3RZRSFSS2B1FS1N3HUB4ABLO4AB163LTB2NS3RZR3RZE3RLR3RSR3RSM3NSR2K2S1N2NS3RZR3RSR3NSRS1N2NS3RZR3RSR3NSRS1N2NS3RZR3RSR3NSRS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RLR2K02K32DXS4CEIL2LO3SB13SB23HspS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO2N02R03HspS4CEIL2LO3SB13SB23HspFS2HBS3HUB4ABLO3RZRS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4UBHI3NSZ2NS3RSRS4UBHI3NSZ2NS3RSRSS3SB3S4CEIL2LO3HPG3SB33SB43HspSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4AB163RZM1H2H02H42H9S4UB161H2H02H4S2LOS4CEIL2LO2N02R03HspFS1N3HUB4ABLO4AB162T03LTB2NS3RZR3RZE3RLR3RSM3NSR2K02K32Ha2X12X2S4CEIL2LO2N12R12Ha1H3HUB4ABLO3RZR2X12X24SHN04SHS03HPG3SB13SB23SB43SB34PW01S3HUB4ABLO3RZRS1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RZR3RLR3RSR3NSR2K21HFSS4CEIL2LO2N02R03HspSF".
assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
unfold AIMG_HI, AINSTANCE in *.
pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
assert (UB16 : UB mod 16 = 0).
{ rewrite HUB. clear -AB16 RZM. Z.div_mod_to_equations. lia. }
word_range sp SPR.
destruct PC as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7).
pose proof (munch_refl (allocBC_WG L sp UB PG pgw n) m) as MU. pose proof (wmono_refl bsegs m) as WM.
box TT0. box CT8. box DJT. box DJC. box DJN. box DJS.
snapshot [(UB - 16, UB)]%Z MUh WMh.
snapshot [(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
(shad UB, shad UB + shlen (n - n mod 8));
(ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z MUq WMq.
box SHP.
step. step. if_cases K0; zify_cond K0. { exfalso. lia. }
zstep. setreg 20 (Z_to_bv 64 UB) ltac:(rewrite HUB; reflexivity).
zstep. zstep.
step. if_cases K1; zify_cond K1.
2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. clear -UB16. Z.div_mod_to_equations. lia. }
zstep.
step. if_cases K2; zify_cond K2. { exfalso. lia. }
lstep.
zstep. zstep. zstep. zstep. zstep.
rewrite (Z.shiftr_eq_0 n 32) by (try lia; apply Z.log2_lt_pow2; lia).
rewrite (Z.shiftr_eq_0 n 48) by (try lia; apply Z.log2_lt_pow2; lia).
sstep. step. step.
step. if_lit.
zstep. zstep. step. zstep.
sstep.
step. if_cases K3; zify_cond K3. { exfalso. lia. }
carry TT0 MUh WMh ltac:(with_box DJT lia).
step.
carry CT8 MUh WMh ltac:(with_box DJC lia).
lstep. zstep. step.
step. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEP' : ADEPOT DI L mm) end.
{ eapply (adi_frame DI); [exact DEP | exact MUh | exact WMh |].
apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
intros a Ha. pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2. lia. }
clear MUh WMh. box HDR.
snapshot (adepot_W L (bv_unsigned sp + -128)) MUd WMd.
box SHA. box SHU.
step. call_sp ((adi_put DI) L RNG).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
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
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- rng _ _ _ => solve_rng
| |- _ => unfold AIMG_HI; lia
end.
lazymatch goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into IDR end.
lazymatch goal with H : ADEPOT DI L _ |- _ => rename H into DEP2 end.
snapshot [(bv_unsigned sp + -128 - 64, bv_unsigned sp + -128); (UB - 16, UB); (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw)]%Z MUp WMp.
carry HDR MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; lia).
carry SHA MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia)). carry SHU MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia)).
clear MUd WMd.
zstep. zstep. zstep.
rewrite Z.lor_0_l. rewrite (Z.mod_small x 4294967296) by lia.
step.
step. if_lit.
step. step. step. zstep. zstep.
setreg 10 (Z_to_bv 64 (shad AB)) ltac:(unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
lstep.
step. if_lit.
step. zstep. zstep.
rewrite (land_align8_48 n) by lia.
step. if_cases K4; zify_cond K4.
-
unbox SHP.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (SHP' : n mod 8 <> 0 -> rw_cells bsegs mm PG [C1 pj]) end.
{ intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
clear SHP MUq WMq.
call (partial_specG RNG n UB PG pgw pj).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption
| |- mem_inv _ _ => assumption
| |- PG = _ => exact HPG
| |- _ = (if _ then _ else _) => exact HPW
| |- rw_cells _ _ 0x99900 _ => exact PC1
| |- rw_cells _ _ 0xa2538 _ => exact PC4
| |- rw_cells _ _ 0xa3220 _ => exact PC5
| |- rw_cells _ _ 0xa1d9c _ => exact PC6
| |- rw_cells _ _ 0x9fd8d _ => exact PP
| |- rng _ _ _ => solve_rng
| |- ~ _ -> rng _ _ _ => exact RSP
| |- ~ _ -> _ => exact SHP'
| |- ablk _ _ => unfold ablk; right; lia
| |- _ => lia
end.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
{ eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).
apply Forall_nil. }
apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
rewrite K4. rewrite K4 in SHU. pose proof SHU as W0. destruct W0 as [[[WF X1] X2] X3]. cbn in WF. destruct sj; [exact SHU| cbn in WF; discriminate].
-
step. step. step.
step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UB (n - n mod 8) 0 lo sj).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
| |- @eq word _ _ => reflexivity
| |- rw_cells _ _ (shad _) _ => exact SHU
end.
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption
| |- rng _ _ _ => solve_rng
| |- ablk _ _ => unfold ablk; right; atop_facts; lia
| |- _ => atop_facts; first [lia | Z.div_mod_to_equations; lia]
end.
unbox SHP.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (SHP' : n mod 8 <> 0 -> rw_cells bsegs mm PG [C1 pj]) end.
{ intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
clear SHP MUq WMq.
call (partial_specG RNG n UB PG pgw pj).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption
| |- mem_inv _ _ => assumption
| |- PG = _ => exact HPG
| |- _ = (if _ then _ else _) => exact HPW
| |- rw_cells _ _ 0x99900 _ => exact PC1
| |- rw_cells _ _ 0xa2538 _ => exact PC4
| |- rw_cells _ _ 0xa3220 _ => exact PC5
| |- rw_cells _ _ 0xa1d9c _ => exact PC6
| |- rw_cells _ _ 0x9fd8d _ => exact PP
| |- rng _ _ _ => solve_rng
| |- ~ _ -> rng _ _ _ => exact RSP
| |- ~ _ -> _ => exact SHP'
| |- ablk _ _ => unfold ablk; right; lia
| |- _ => lia
end.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
{ eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).
apply Forall_nil. }
apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithDepot.
End CANSEC1.
