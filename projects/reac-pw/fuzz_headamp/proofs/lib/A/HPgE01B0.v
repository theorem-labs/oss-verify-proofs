(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections other than
   .note.gnu.build-id are byte-equal to the pin's): the helpers of part 3 of segment E01 of the walk of LLVMFuzzerTestOneInput, the
   body 0x80dfc -> the malloc entry 0x53060 (lib/A/HPgE01D.v e01_body_stmt). Proves no function
   (kind: helpers of a segment lemma).

   What is here:
   - the arithmetic of the two harness bytes: the compiler's division by ten at 0x80e6c .. 0x80e80
     (b - 10 * ((205 b) >> 11) = b mod 10 for a byte b) and the null flag b & 1;
   - the geometry of the real frame: R = 32 * ((S - 0x1e0) / 32) lies in (S - 0x200, S - 0x1e0];
   - what a run keeps outside its write window, and the carried cells / the frame shadow / the input bytes
     across such a run;
   - the two start states of the body's runs (the only writable region is the null-flag slot R+0x40; the
     input's shadow byte and its first bytes are read-only regions at the atoms the checks use);
   - the three shapes of the input left after the two harness bytes (nothing, nothing after one byte, and
     the bytes after two), in the form lib/A/HPgE01D.v e01_in asks for. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSegM HPgCalls HPgMem HPgSteps HPgE01D.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================== 1. arithmetic ======================================== *)
(* `li a1,205; mul a1,a0,a1; srli a1,a1,0xb; li a2,10; mul a1,a1,a2; sub s8,a0,a1` 0x80e6c .. 0x80e80. *)
Lemma e01b_mod10 : forall b, 0 <= b < 256 -> b - 10 * (205 * b / 2048) = b mod 10.
Proof.
intros b Hb.
pose proof (Z.div_mod b 10 ltac:(lia)) as D. pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as M.
assert (Hq : 0 <= b / 10 <= 25) by lia.
assert (E : 205 * b = (b / 10) * 2048 + (2 * (b / 10) + 205 * (b mod 10))) by lia.
rewrite E, Z_div_plus_full_l by lia.
rewrite (Z.div_small (2 * (b / 10) + 205 * (b mod 10)) 2048) by lia.
lia.
Qed.
(* `andi a1,a1,1` 0x80e20 *)
Lemma e01b_land1 : forall b, 0 <= b -> 0 <= Z.land b 1 <= 1.
Proof. intros b Hb. exact (Z_land_upper b 1 ltac:(lia)). Qed.
(* R = (S - 0x1e0) & -32, as hq_geo states it *)
Lemma e01b_geo : forall S R, R = 32 * ((S - 0x1e0) / 32) -> S - 0x200 < R <= S - 0x1e0.
Proof.
intros S R ->. pose proof (Z.div_mod (S - 0x1e0) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (S - 0x1e0) 32 ltac:(lia)) as M. lia.
Qed.
(* the shadow byte of an address below the allocator's ceiling is far below it *)
Lemma e01b_sh_low : forall {rc : YM05.RunCeil} p, 0 <= p -> p <= alloc_ceiling ->
0 <= shadow_of_addr SHADOW_OFF p < alloc_ceiling.
Proof.
intros rc p H0 H1. pose proof YM05.alloc_ceiling_val as [Hc _]. unfold shadow_of_addr, SHADOW_OFF.
assert (Hd : 0 <= p / 8 <= 17592184995840) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
lia.
Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ============================ 2. what a run keeps outside its windows ============================ *)
Lemma e01b_keep : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Lemma e01b_garr8_keep : forall H H' (m m' : word -> option byte) a l,
garr8 rsegs (mrestrict H m) a l ->
(forall j, (j < length l)%nat -> aview rsegs H' m' (a + Z.of_nat j) = aview rsegs H m (a + Z.of_nat j)) ->
garr8 rsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l G K j Hj. destruct (G j Hj) as [V Hb]. split; [|exact Hb].
apply (val_mem_kept rsegs H H' m m' (a + Z.of_nat j) 1 _); [|exact V].
intros k Hk. replace k with 0 by (cbn in Hk; lia). rewrite Z.add_0_r. exact (K j Hj).
Qed.
Lemma e01b_garr8_tl : forall m a x l, garr8 rsegs m a (x :: l) -> garr8 rsegs m (a + 1) l.
Proof.
intros m a x l G j Hj. destruct (G (S j) ltac:(cbn; lia)) as [V Hb]. cbn [nth] in V, Hb. split; [|exact Hb].
replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. exact V.
Qed.
Lemma e01b_garr8_tl2 : forall m a x y l, garr8 rsegs m a (x :: y :: l) -> garr8 rsegs m (a + 2) l.
Proof.
intros m a x y l G. replace (a + 2) with (a + 1 + 1) by lia.
exact (e01b_garr8_tl m (a + 1) y l (e01b_garr8_tl m a x (y :: l) G)).
Qed.

(* ============================ 3. reading the state a run ends at ============================ *)
Lemma e01b_reg : forall H E ss ms (r : bv 5) v,
st_ok rsegs E ss (restrict H ms) -> sv_denot E (sr_get (ss_regs ss) r) = w64 v ->
getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r v HS Hd. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS). exact Hd. Qed.
Lemma e01b_cell : forall E m (k : nat) b cs lo hi wlo whi off e v,
region_ok rsegs E m (YP09.mkRegion (Some k) lo hi wlo whi cs) -> bv_unsigned (ew E k) = b ->
In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
val_mem rsegs m (b + off) 8 v.
Proof.
intros E m k b cs lo hi wlo whi off e v Hr Hk Hin Hd Hv.
destruct Hr as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
cbn [YP09.r_base base_val] in Hck. rewrite Hk in Hck.
exact (val_of_chunk_ok rsegs E m b off 8 e v Hck Hd ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
End g.

(* ============================ 4. the run's quantities and the carried cells ============================ *)
(* The body fixes S, R, F (hq_geo), the input cursor and what is left of it, the cap and the null flag; the four
   blocks and rc are free (the next part's malloc gives pp). *)
Definition e01b_env (S R F src left cap null : Z) (rest : list byte) : hd_env :=
  HDEnv S R F 0 0 0 0 (hd_len rest) cap null 0 src left.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the thirteen saves at [S - 0x68, S), the three float saves at [S - 0x80, S - 0x68) and the frame's
   flag-pointer word at F + 0x3f8, across a run whose only window is [lo, hi) *)
Lemma e01b_kept_keep : forall (hx : hq_hcx rsegs) pos e (W : world rsegs) mem mem' regs regs' lo hi,
hq_kept rsegs hx pos e W mem regs ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) mem x) ->
0 <= e_S e - 0x80 -> e_S e < 2 ^ 64 -> 0 <= e_F e -> e_F e + HQ_FLAG + 8 <= 2 ^ 64 ->
(hi <= e_S e - 0x80 \/ e_S e <= lo) -> (hi <= e_F e + HQ_FLAG \/ e_F e + HQ_FLAG + 8 <= lo) ->
hq_kept rsegs hx pos e W mem' regs'.
Proof.
intros hx pos e W mem mem' regs regs' lo hi [Hc Hf] K HS0 HS1 HF0 HF1 DS DF.
assert (KS : forall b o, (hd_xv e b = e_S e /\ -0x80 <= o <= -8) \/ (hd_xv e b = e_F e /\ o = HQ_FLAG) ->
  hm_keeps rsegs (w_H W) mem (w_H W) mem' regs regs' e (LCell b o)).
{ intros b o Hb. cbn [hm_keeps]. intros i Hi.
  destruct Hb as [[Eb Ho] | [Eb Ho]]; rewrite Eb; apply K; unfold HQ_FLAG in *; lia. }
split.
- apply (hm_atl_kept rsegs (w_H W) mem (w_H W) mem' regs regs' e _ Hc).
  intros f Hin. unfold hq_cells in Hin. apply in_app_or in Hin. destruct Hin as [Hin | [<- | []]].
  + unfold hq_saves_L in Hin. apply in_map_iff in Hin as (j & <- & Hj). apply in_seq in Hj.
    cbn [fst]. apply KS. left. cbn [hd_xv]. split; [reflexivity | lia].
  + cbn [fst]. apply KS. right. cbn [hd_xv]. split; [lia | reflexivity].
- destruct Hf as (v0 & v1 & v2 & H0 & H1 & H2). exists v0, v1, v2.
  split; [|split].
  + apply (hm_at_kept rsegs (w_H W) mem (w_H W) mem' regs regs' e (LCell XS (- 0x70)) v0 H0).
    apply KS. left. cbn [hd_xv]. split; [reflexivity | lia].
  + apply (hm_at_kept rsegs (w_H W) mem (w_H W) mem' regs regs' e (LCell XS (- 0x78)) v1 H1).
    apply KS. left. cbn [hd_xv]. split; [reflexivity | lia].
  + apply (hm_at_kept rsegs (w_H W) mem (w_H W) mem' regs regs' e (LCell XS (- 0x80)) v2 H2).
    apply KS. left. cbn [hd_xv]. split; [reflexivity | lia].
Qed.
End k.

(* ================================ 5. the start states of the body's runs ================================
   The only writable region is the null-flag slot R+0x40 (`sd a1,64(s1)` 0x80e24 / `sd zero,64(s1)` 0x80e3c);
   the shadow byte of the input (atom 32, the alias the two checks' `srli; add` forms) and its first one or two
   bytes (atom 27 = the cursor) are read-only one-byte regions. *)
Definition E01B_R40 : YP09.region := YP09.mkRegion (Some 9%nat) 0x40 0x48 0x40 0x48 [].
Definition e01b_sh (v : sv) : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 v)].
Definition e01b_dat (dhi : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 27%nat) 0 dhi 0 0 cs.
Definition e01b_extra (sa b0 b1 : Z) : list word := [w64 sa; w64 b0; w64 b1].
Definition e01b_atoms (f : list (nat * afact)) : list (nat * afact) :=
  (27%nat, mkAF 4096 (2 ^ 47) 4) :: (33%nat, mkAF 0 255 0) :: (34%nat, mkAF 0 255 0) :: f.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* n = 0: no input byte is read, so the slot is the only region *)
Lemma e01b_entry0 : forall (W : world rsegs) regs mem R sr,
regs_ok (Ereg regs []) sr regs ->
getr regs 9 = w64 R -> 0 <= R -> R + 0x48 <= 2 ^ 64 ->
(forall o, 0x40 <= o < 0x48 -> apresent (w_H W) mem (R + o)) ->
st_ok rsegs (Ereg regs []) (mkSS E01_HDR sr [E01B_R40] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (w64 E01_HDR) mem (seg_rom rsegs))).
Proof.
intros W regs mem R sr HR H9 HR0 HR1 HP. rewrite restrict_mkst_fx.
assert (U9 : bv_unsigned (ew (Ereg regs []) 9) = R).
{ rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
apply (entry_st_ok_full rsegs).
- exact HR.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold E01B_R40, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable rsegs). apply HP. lia.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [exact I | split; exact I].
Qed.

(* n > 0: the slot, the input's shadow byte (value shv at atom 32) and its first dhi bytes (atom 27) *)
Lemma e01b_entryN : forall (W : world rsegs) regs mem R p sa b0 b1 dhi cs f sr shv al,
regs_ok (Ereg regs (e01b_extra sa b0 b1)) sr regs ->
getr regs 9 = w64 R -> getr regs 27 = w64 p ->
0 <= R -> R + 0x48 <= 2 ^ 64 -> alloc_ceiling <= R + 0x40 ->
(forall o, 0x40 <= o < 0x48 -> apresent (w_H W) mem (R + o)) ->
region_ok rsegs (Ereg regs (e01b_extra sa b0 b1)) (mrestrict (w_H W) mem) (e01b_sh shv) ->
region_ok rsegs (Ereg regs (e01b_extra sa b0 b1)) (mrestrict (w_H W) mem) (e01b_dat dhi cs) ->
regions_wf [E01B_R40; e01b_sh shv; e01b_dat dhi cs] = true ->
sa = shadow_of_addr SHADOW_OFF p -> 4096 <= p -> p mod 16 = 0 -> 0 < dhi ->
p + dhi <= alloc_ceiling -> in_app p dhi ->
0 <= b0 < 256 -> 0 <= b1 < 256 ->
atoms_ok (Ereg regs (e01b_extra sa b0 b1)) f ->
alias_ok (Ereg regs (e01b_extra sa b0 b1)) al ->
st_ok rsegs (Ereg regs (e01b_extra sa b0 b1))
  (mkSS E01_HDR sr [E01B_R40; e01b_sh shv; e01b_dat dhi cs] None (mkFacts (e01b_atoms f) [] al))
  (restrict (w_H W) (mkst regs (w64 E01_HDR) mem (seg_rom rsegs))).
Proof.
intros W regs mem R p sa b0 b1 dhi cs f sr shv al HR H9 H27 HR0 HR1 HRc HP HSh HD Hwf Esa Hp4 Hp16 Hd0 Hpc Happ Hb0 Hb1 HF HA.
rewrite restrict_mkst_fx.
set (E := Ereg regs (e01b_extra sa b0 b1)).
pose proof YM05.alloc_ceiling_val as [Hcl _].
assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
assert (U9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U27 : bv_unsigned (ew E 27) = p).
{ subst E. rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27. unfold w64. apply unsigned_lit_small. lia. }
assert (Hsa : 0 <= sa < alloc_ceiling) by (subst sa; apply e01b_sh_low; lia).
assert (U32 : bv_unsigned (ew E 32) = sa).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth e01b_extra]. unfold w64. apply unsigned_lit_small. lia. }
assert (Hp8 : p = 8 * (p / 8)).
{ pose proof (Z.div_mod p 16 ltac:(lia)) as D16. pose proof (Z.div_mod p 8 ltac:(lia)) as D8.
  assert (p mod 8 = 0) by (rewrite D16, Hp16, Z.add_0_r, Z.mul_comm;
    replace (p / 16 * 16) with ((p / 16 * 2) * 8) by lia; apply Z_mod_mult). lia. }
apply (entry_st_ok_full rsegs); change (Ereg regs (e01b_extra sa b0 b1)) with E.
- exact HR.
- exact Hwf.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold E01B_R40, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply HP. lia.
  + exact HSh.
  + exact HD.
- apply pairwise_disjoint_of_extents.
  unfold E01B_R40, e01b_sh, e01b_dat, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U27, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_of_addr, SHADOW_OFF in *.
  revert Esa Happ Hsa Hp4 Hp8 Hpc Hd0 HRc Hcl. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact HA]].
  unfold e01b_atoms. cbn [atoms_ok]. split; [|split; [|split; [|exact HF]]]; unfold afact_ok;
  cbn [af_lo af_hi af_al2].
  + rewrite U27. change (2 ^ 4) with 16. split; [lia|]. split; [exact Hp16 | lia].
  + assert (U33 : bv_unsigned (ew E 33) = b0).
    { subst E. rewrite (ew_Ereg_extra regs _ 1). cbn [nth e01b_extra]. unfold w64. apply unsigned_lit_small. lia. }
    rewrite U33, Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
  + assert (U34 : bv_unsigned (ew E 34) = b1).
    { subst E. rewrite (ew_Ereg_extra regs _ 2). cbn [nth e01b_extra]. unfold w64. apply unsigned_lit_small. lia. }
    rewrite U34, Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
Qed.
End e.

(* ================================ 6. the input after the two harness bytes ================================ *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

(* the empty input: the harness's caller passes the address of an empty object *)
Lemma e01b_in_0 : forall (hx : hq_hcx rsegs) (W : world rsegs) mem S R F pe,
h_pl rsegs hx = [] -> 0 < pe -> pe < kLowMemEnd ->
e01_in B hx W mem (e01b_env S R F pe 0 0 0 []) [].
Proof.
intros hx W mem S R F pe Hpl H0 H1. unfold e01_in, hq_harn, e01b_env.
cbn [e_S e_R e_F e_len e_cap e_null e_src e_left]. rewrite Hpl.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; lia.
- reflexivity.
- reflexivity.
- cbn [hd_zbytes map]. apply garr8_nil.
- exact H0.
- unfold kLowMemEnd in H1. lia.
- unfold amem_range, kLowMemEnd in *. lia.
- left. reflexivity.
Qed.

(* one input byte: the null flag is its low bit, the cap is 0 and nothing is left *)
Lemma e01b_in_1 : forall (hx : hq_hcx rsegs) (W : world rsegs) mem S R F p b0,
h_pl rsegs hx = [b0] -> 4096 <= p -> p + 1 <= alloc_ceiling -> in_app p 1 ->
e01_in B hx W mem (e01b_env S R F (p + 1) 0 0 (Z.land (bv_unsigned b0) 1) []) [].
Proof.
intros hx W mem S R F p b0 Hpl Hp4 Hpc Happ. unfold e01_in, hq_harn, e01b_env.
cbn [e_S e_R e_F e_len e_cap e_null e_src e_left]. rewrite Hpl.
pose proof (bv_unsigned_in_range 8 b0) as Hb0. change (bv_modulus 8) with 256 in Hb0.
pose proof (e01b_land1 (bv_unsigned b0) ltac:(lia)) as Hl.
pose proof YM05.alloc_ceiling_val as [Hcl _].
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- cbn [skipn Cursor.fuzz_u8 fst snd].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; lia.
- reflexivity.
- reflexivity.
- cbn [hd_zbytes map]. apply garr8_nil.
- lia.
- lia.
- unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd, ASAN_CEIL in *. lia.
- left. reflexivity.
Qed.

(* two or more input bytes: the null flag, the cap and the bytes after them *)
Lemma e01b_in_2 : forall (hx : hq_hcx rsegs) (W : world rsegs) mem S R F p n b0 b1 rest,
h_pl rsegs hx = b0 :: b1 :: rest -> n = Z.of_nat (length (b0 :: b1 :: rest)) ->
In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) ->
4096 <= p -> p + req_size n <= alloc_ceiling -> in_app p (req_size n) ->
garr8 rsegs (mrestrict (w_H W) mem) (p + 2) (hd_zbytes rest) ->
e01_in B hx W mem (e01b_env S R F (p + 2) (n - 2) (bv_unsigned b1 mod 10) (Z.land (bv_unsigned b0) 1) rest) rest.
Proof.
intros hx W mem S R F p n b0 b1 rest Hpl Hn Hin Hp4 Hpc Happ HG. unfold e01_in, hq_harn, e01b_env.
cbn [e_S e_R e_F e_len e_cap e_null e_src e_left]. rewrite Hpl.
pose proof (bv_unsigned_in_range 8 b0) as Hb0. change (bv_modulus 8) with 256 in Hb0.
pose proof (bv_unsigned_in_range 8 b1) as Hb1. change (bv_modulus 8) with 256 in Hb1.
pose proof (e01b_land1 (bv_unsigned b0) ltac:(lia)) as Hl.
pose proof (Z.mod_pos_bound (bv_unsigned b1) 10 ltac:(lia)) as Hm.
pose proof YM05.alloc_ceiling_val as [Hcl _].
cbn [length] in Hn.
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- cbn [skipn Cursor.fuzz_u8 fst snd].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; lia.
- lia.
- reflexivity.
- exact HG.
- lia.
- lia.
- unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd, ASAN_CEIL in *. lia.
- right. exists p, n. split; [exact Hin|]. lia.
Qed.
End i.

Print Assumptions e01b_mod10.
Print Assumptions e01b_entryN.
Print Assumptions e01b_kept_keep.
