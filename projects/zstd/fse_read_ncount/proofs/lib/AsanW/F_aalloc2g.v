(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase ADepot_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 AModelFacts APrimFacts F_memset F_apoison F_aalloc_s.
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
F (Z_to_bv 64 0x329e8) fc None m' (seg_rom asegs)
/\ munch (allocBC_WG L sp UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -128)
/\ 0 < id < 2^31
/\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 (hdr_b1_mid b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
/\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
/\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
/\ ADEPOT DI L m'.
#[using="Type"] Lemma partial_specG : forall RNG (n UB PG pgw : Z) (pj : byte) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem),
mem_inv asegs m ->
1 <= n -> PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
ablk UB (UB + n) -> UB + n <= ATOP -> UB mod 8 = 0 ->
rw_cells asegs m 0x99770 [C8 (Z_to_bv 64 0x133fa8); C8 (Z_to_bv 64 0x9fc78); C8 (Z_to_bv 64 0xa2478);
C8 (Z_to_bv 64 0xa3168); C8 (Z_to_bv 64 0xa3170); C8 (Z_to_bv 64 0xa3160)] ->
rw_cells asegs m 0xa2478 [C8 (Z_to_bv 64 0x7fff8000)] ->
rw_cells asegs m 0xa3160 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
rw_cells asegs m 0xa1cdc [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m 0x9fccd [C1 (Z_to_bv 8 1)] ->
(n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
rng_aimg RNG -> (n mod 8 <> 0 -> rng RNG PG 1) ->
evtF asegs RNG (fun ms' => exists ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' m',
ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 UB) s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x329e8) fc None m' (seg_rom asegs)
/\ munch [(PG, PG + pgw)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))]))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 UB) s5 (Z_to_bv 64 (n - n mod 8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32954) fc None m (seg_rom asegs)).
Proof.
intros until m. intros MI N HPG HPW UBLO UBHI UB8 GOT SHB LAY CANP PP SHP RIMG RPG.
pose proof (munch_refl [(PG, PG + pgw)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold ablk, AIMG_HI, KLS in UBLO. atop_facts.
assert (SHR : 0x7fff8000 <= shad UB /\ 0 <= shlen (n - n mod 8) /\ PG + 1 <= 0x10007fff8000).
{ unfold shad, shlen, ASHOFF in *. Local Ltac2 Set LiaHints.tbl := fun () => "00f0>11383758314.6911385855457.7316630097935.6020605729586.5723495003441.5823495003830.6127238478433.5928277756440.5928277756440.6228913119921.7028915217076.6628915217081.7229782367974.5729784416474.6129784417117.5829888602459.5929888602459.6233858871586.5933858871586.623664093147.70 3664093147.74 41385966171.5941385966171.6242328825979.5942328825979.6252076332701.6855019083177.7055019083177.7455148979235.6055148979362.6155148980005.5855148980132.5955157802157.6955157802157.7255338713179.5955338713179.625646954331.59 5646954331.62 59308548964.6059308628433.5959308628566.6059308628695.6159588178609.7059663788513.9359663788513.9661884731502.5961929812114.5961929812241.5861929812630.6161937685146.6861939782289.748010146619.59 8010146619.62 8443034364.78 00000100200?00@00A00B00M00Q00U00V00W00X00Y00Z00[00d00m00n00o01001101:01C01L01U01V01W01X01_01f02<02I02[02b02k03403=03F03T03a03n04C04D05105\05k06:06L06^07007B07G07L084SSS1N4UBLO2K01eSSSS1N4UBLO2K0S2HBS2HBSSSSSSS3HPG3SHRS3HPG3SHRSSSSS3HPG3SHRS3HPG3SHRS3HPG3SHRS3HPG3SHRFSSS2K12K2S2K12K2S1N4UBLO4UBHI3UB81H2K0S1N4UBHI1H2K1S1N4UBLO3UB82K02K1S2K12K2S3HPG3SHRS3HPG3SHRS3HPG3SHRS3HPG3SHRS1N4UBLO2K02NES1N4UBHI1H2K2S1N4UBHI1H2K3S1N4UBLO3UB82K02K12K4SS1N3UB82K02K12H02H12H52H63H103H113H153H163H20S3UB82K02K42H02H12H52H63H103H113H153H163H20S1N4UBLO4UBHI1HS1N4UBLO4UBHI1HS1N4UBLO4UBHI1H2K0S1N4UBLO4UBHI1H2K0S1N4UBLO4UBHI1H2K0S1N4UBLO4UBHI1H2K0S3SHRS3SHRS1N3HPG4UBLO4UBHI3UB81H2H02H52H63H103H11".
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
stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
mem_inv asegs m ->
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
rw_cells asegs m (bv_unsigned sp + -128)
[CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
0 <= b1 < 256 ->
rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sj] ->
(n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
poison_cells m -> rw_cells asegs m 0x9fccd [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
ADEPOT DI L m ->
AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
rng RNG (UB - 16) 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
evtF asegs RNG (allocBC_postG L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
(MS (mkR (Z_to_bv 64 0x3273c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
(Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
(Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
t3 t4 t5 t6)
F (Z_to_bv 64 0x3273c) fc None m (seg_rom asegs)).
Proof.
intros until s11v.
intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.
Local Ltac2 Set LiaHints.tbl := fun () => "04D0?10274798654.14910274798654.15010313444268.4  1047820382.152 10625553216.15210669833637.17610721241625.16311191675278.2  11204126542.16311479870031.17211752483811.12312428150072.19112480772618.1691324746171.160 1324746171.163 13313577562.3  13336768858.16313367089074.1781343986644.172 14168905729.4  14274249110.18214276346290.19714311754318.17914651424458.3  1476722482.197 1478819606.182 14894876594.19714896973718.18215319906838.17315335882954.3  15830019643.16315948676913.4  15949560227.19216346643763.17716486372681.17016512576796.14816528622318.16316545774130.5  16557567661.16816557567661.183168876862.149  168876862.150  17133062962.3  1728976368.170 17833946714.3  17949008832.17317949008832.18817986879152.15217986879152.17018430975599.16119117323662.2  19352503472.16319517033132.16819517033132.18319682054918.15220158040118.17720322563816.3  20719413306.16321195996626.14921388346286.16321969407398.14922718042091.16822718042091.17022718042091.18323039802350.17923132879118.4  24211191904.4  2431248216.149 24982578737.1472499582526.149 2499582526.150 25076071819.19125076071819.19225157604214.15225860023374.1632597469155.177 25996042971.15226403658112.16027199765278.4  27775112880.4  27943014742.4  28001526702.16328040491972.19228485987241.16228729582384.5  29782367974.14829782367974.16929965292900.16829965292900.18330430348547.15830507154306.14630517090690.18030613629521.15130956271566.16331192993456.16331366954517.15232377744366.17932475639163.17932932373168.4  33082065689.17933262659552.14933262659552.15033445853437.2  33577178314.14933577178314.15033875467557.1703392152800.159 34028498699.3  34029725987.19234170950174.14934170950174.15034243631625.17434755885818.17935289778563.16135293574422.17036254216601.15936254216601.16036254216601.16336376561033.4  36534319948.4  36635088727.15036701002830.16336702058843.14936967174608.16337562289838.1633781219151.172 38606657699.192386431922.197  3879545503.172 388529046.182  39467920654.17939896594704.17940836900654.16341030367075.17441792303450.163423940875.3    42677208786.14942805740039.19143567419058.19743569516182.18243837609629.4  44820102307.14944820102307.15044820102307.16345221239098.17945480795915.3  45699881561.1634573656713.2   45738189427.19245891680928.18245893778052.19746268607598.17946298861963.16046988300803.12347039319577.16347244432302.14947244432302.15048240491802.16248242588945.15848242588946.15948738442331.14948865763193.2  49181239354.16349750950894.17949978085870.17950645046474.14950645046474.15050667478351.17250734000704.17451046289722.15951048386864.16251561310307.19251683311886.16351749720470.18751816630506.14951816630506.15052136437230.17952523015482.15952567164907.14952567164907.15052567164907.16352567164907.17952569147371.17252579502455.17252579502455.17352682867945.14952682867945.15052736796155.5  5281887934.149 5281887934.150 53493744851.16854224864146.17054404701703.17254605059791.17255242965934.16355473260884.14856091204670.14956091204670.15056102654486.17756115695737.19756117792861.18256170256219.17256170498639.15156339402826.3  56956174629.15257022093363.1705750404535.182 57730438550.18257732535730.19757821142078.14957821142078.15058174797435.16358369446314.16958477402019.19258730541225.18258732638349.19758840920286.16358987689625.17958998195513.16359039346094.16359314873579.14759314873579.14959314873579.1515932235838.149 5932235838.150 59338331354.16359586081466.17760385159294.17960795071034.16261482382924.15161560206755.19261671386902.15861673380011.5  61860850094.16361884732010.16961937685145.15961939782289.16161939782290.1806201887545.152 62722810255.1726298254074.179 63142967631.17263999581114.2  64026414714.16364144173150.14964144173150.15064229420110.16364738246334.16364897170030.16864897170030.18364996132282.16265128844401.17065164961555.19265204828578.16165299792814.16366028155702.15566028155702.17366149329551.25 66151427842.16 66330498723.16066706099278.16367180176575.5  67469470029.15567469470029.44 68136883746.19768138980870.18268398178269.17068427648078.16368565691470.1638116721570.160 8264524782.179 8646118925.1   9471306659.192 9748552662.182 9750649842.197 9959001935.172 00000>00L00M00T00]00^00_00`00n01A01B01C01D01E01F01G01e01f01g01h02902J02N02O02`03103B03S03d03e03f03g04<04=04j05N05R05S06106O06]06k06l07a07b09F0:m0;30;90;:0;;0;<0;A0;F0;K0;L0;Q0;k0;l0<:0<>0<_0=@0=a0=o0>00>10>40>50>C0>Q0?60?h0?o0@=0@>0@C0@a0@b0@c0@d0A20AK0AL0AM0AN0AO0AR0AU0AV0Am0BD0BE0BS0C40Ca0Co0D00D10D20DS0E40E50ES0F10F50F60F;0FP0FT0FX0Fh0GF0GG0GH0GI0GJ0GK0GL0GM0Gj0H80HH0Hi0I70IJ0I_0J00JC0JT0Jb0KC0KQ0KR0Kl0L10L20L30LD0LU0LV0LW0LX0LY0L]0Lb0M;0M<0MQ0ND0O70OE0OF0OG0OH0Oe0PB0PC0PD0PE0PU0PV0Q40QB0QP0Qj0RD0RW0Rn0Ro0S00SE0SI0SJ0SN0SR0S`0Sa0Sb0Sc0Sd0Se0UW0V20V30VL0Ve0Vf0W40WB0WG0X00X10XD0XR0Xi0Y70YE0YJ0Y`0Z60Z;0Z<0Z=0ZA0ZB0ZG0ZX0Zi0[70[E0[F0[X0[m0\<0\K0\h0]A0]Z0]h0^10^@0^S0^a0^o0_30_40_Q0_R0_S0_h0_l0_m0`;0`n0a@0aR0ad0bQ0bd0c>0cQ0cR0cV0cd0d20d@0d]0dn0e?0e@0eE0e^0e_0em0f<0fK0f`0fn0g20g@0gA0h?0iI0iZ0ik0j\0jj0k80k90kG0kH0k]0kn0l?0lRS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS2N12R1S3SZB3LTBSSFS3HUB4ABLO3RZRS4CEIL2LO2N02R03HspSFSSSFS3HUB4ABLO3HPG3SB23SB33SB43RZRSFFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S2HBSS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S4CEIL2LO3CX13HspSSFS4CEIL2LO3SB13SB23HspSS1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RZR3RLR3RSR2K21HS1N3HUB4ABLO4UBHI3NSZ2NS3RZR3RSR3NSRS2HBFS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRS3HUB4ABLO3RZRS3HUB4ABLO3RZRFS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RLR3RSR3RSM2K02K32K4FS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RLR3RSR3RSM3NSR2K02K32NE4SHN04SHS01HS4CEIL2LO1N3HUB4ABLO4AB163HPG3SB13SB23SB33SB42T03LTB2NS3RZR3RZE3RLR3RSR3RSM3NSR2K02K32K42NE4SHN04SHS01HS4CEILS4CEILSFSS3HPGS3HPGS3S47FS3HspS3HUB4ABLO3HPG3SB33SB43RZRFS3HUB4ABLO3RZRS2B1S1N3HUB4ABLO4AB163LTB3RZR3RZE3RLRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLRS3HUB4ABLO3RZRFSS1NSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS4CEIL2LO3HPG3SB23SB33SB43Hsp3LTB3SPSS4CEIL2LO3HUB4ABLO4UBHI3NSZ3HPG3SB42NS3RZR3RSR3HspS2N02R0S3HUB4ABLO3RZRSS3SPSS3HUB4ABLO4UBHI3NSZ2NS3RZR3RSRFFFS3HUB4ABLO3RZRS4CEIL2LO3HPG3SB43SPS3HspSSSSS1NS1NSS3HUB4ABLO4UBHI3NSZ3NSRS3HUB4ABLO4UBHI3NSZ3NSRSS3HUB4ABLO3RZRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RLR2K02K32DXS3HUB4ABLO3RZRSFSS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRFS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3HPG3SB23SB33SB43RZRS2LOSS3HspS4CEIL2LO3SB13SB23HspS2HBS2HBS4CEIL2LO2T13HspS3HUB4ABLO3HPG3SB23SB33SB43RZRSSSSSFSS1N4ABLO2T02T13LTB3RZR3RLR2K0S3HUB4ABLO3RZRS2NS3RZR3RSR3NSRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS3HUB4ABLO3RZRS4CEIL2LO2N02R03HspS4CEIL2LO3SB13SB23HspS3HPG3SB13SB23SB3S4CEIL2LO2N02R03HspS3HPG3SB13SB23SB3S3HUB4ABLO3RZRS4CEIL2LO4UBHI3NSZ3LTB3SPS2NS3RSRS3HUB4ABLO3RZRFS3HUB4ABLO3HPG3SB33SB43RZRS3HspFFS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3FSSSS2HBS3HspS4CEIL2LO4UBHI3NSZ2NS3RSRSS4CEIL2LO3SB13SB23HspS3HUB4ABLO3SB44PW013RZR3HPG3SB33SB24CEIL2LO3LTB3SPSS3HPG3SB33HUB4ABLO3SB44PW013RZR3SB24CEIL2LO3LTB3SPSS3HUB4ABLO3RZRSSSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRSSSS2NS3RZR3RSR3NSRFS3HUB4ABLO3HPG3SB23SB33SB43RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3HPG3SB33SB43RZRS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO2N02R03HspS4CEIL2LO3SPS2N12R13HspSSS4CEIL2LO3SB13SB23HspS2HBSS2HBS2HBS3HUB4ABLO3RZRSSSSSS4CEIL2LO1N3HUB4ABLO4UBHI4AB163NSZ2T03LTB2N12R12NS3RZR3RZE3RLR3RSR2K02K32X12X21H3HPG3SB13SB23SB33SB44SHN04SHS03RSMS4CEIL2LO2N12R13Hsp3LTB3SPSFS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRFS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3IDRS1N3HUB4ABLO4AB163LTB3RZR3RZE3RLR3RSR3RSMFS4CEIL2LO2N02R03HspS3HUB4ABLO3RZRS3HUB4ABLO4UBHI3NSZ3NSRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3IDRS4CEIL2LO3SB43SPS4PW01S4CEIL2LO3SB43SPS4PW01S3HspSFS2LOSS3IDRS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S3HUB4ABLO3RZRS3HUB4ABLO3RZRSS1N2NS3RZR3RSR3NSRS4CEIL2LO3SB13SB23HspS4CEIL3SB44PW01S4CEIL3SB44PW01S4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS4CEIL2LO4UBHI3NSZ2NS3RSRS3HUB4ABLO3RZRS4ABLO2K0S3HUB2NS3RSR2K2S4ABLO2T03LTB2K02K3S3HUB4ABLO3RZRS3HUB4ABLO3RZRS2HBSS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRSSS4CEIL2LO3SB13SB23HspS2B1FS3HUB4ABLO3RZRS1N3HUB4ABLO4AB163LTB2NS3RZR3RZE3RLR3RSR3RSM3NSR2K2S1N2NS3RZR3RSR3NSRS1N2NS3RZR3RSR3NSRS1N2NS3RZR3RSR3NSRS1N3HUB4ABLO4AB162T03LTB3RZR3RZE3RLR2K02K32DXS4CEIL2LO2N02R03HspS3HUB4ABLO3HPG3SB33SB43RZRS4CEIL2LO2N02R03HspFS2HBS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS4CEIL2LO4UBHI3NSZ3SPS2NS3RSRS4UBHI3NSZ2NS3RSRS4UBHI3NSZ2NS3RSRSS3SB3S4CEIL2LO3HPG3SB33SB43HspSS3HUB4ABLO3RZRS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4AB163RZM1H2H02H42H9S4UB161H2H02H4S2LOS3HUB4ABLO3RZRFS1N3HUB4ABLO4AB162T03LTB2NS3RZR3RZE3RLR3RSM3NSR2K02K32Ha2X12X2S4CEIL2LO2N12R12Ha1H3HUB4ABLO3RZR2X12X24SHN04SHS03HPG3SB13SB23SB43SB34PW01S3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S1N3HUB4ABLO4UBHI3NSZ3LTB2NS3RZR3RLR3RSR3NSR2K21HS3HUB4ABLO3RZRS3HUB4ABLO3RZRSS3HUB4ABLO3RZRSS4CEIL2LO3SB13SB23HspS3HPG3SB13SB23SB3S3HPG3SB13SB23SB3S4CEIL2LO2N02R03Hsp".
assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
unfold AIMG_HI, AINSTANCE in *.
pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
assert (UB16 : UB mod 16 = 0).
{ rewrite HUB. clear -AB16 RZM. Z.div_mod_to_equations. lia. }
word_range sp SPR.
destruct PC as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7).
pose proof (munch_refl (allocBC_WG L sp UB PG pgw n) m) as MU. pose proof (wmono_refl asegs m) as WM.
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
assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
{ intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
clear SHP MUq WMq.
call (partial_specG RNG n UB PG pgw pj).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption
| |- mem_inv _ _ => assumption
| |- PG = _ => exact HPG
| |- _ = (if _ then _ else _) => exact HPW
| |- rw_cells _ _ 0x99770 _ => exact PC1
| |- rw_cells _ _ 0xa2478 _ => exact PC4
| |- rw_cells _ _ 0xa3160 _ => exact PC5
| |- rw_cells _ _ 0xa1cdc _ => exact PC6
| |- rw_cells _ _ 0x9fccd _ => exact PP
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
assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
{ intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
clear SHP MUq WMq.
call (partial_specG RNG n UB PG pgw pj).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption
| |- mem_inv _ _ => assumption
| |- PG = _ => exact HPG
| |- _ = (if _ then _ else _) => exact HPW
| |- rw_cells _ _ 0x99770 _ => exact PC1
| |- rw_cells _ _ 0xa2478 _ => exact PC4
| |- rw_cells _ _ 0xa3160 _ => exact PC5
| |- rw_cells _ _ 0xa1cdc _ => exact PC6
| |- rw_cells _ _ 0x9fccd _ => exact PP
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
