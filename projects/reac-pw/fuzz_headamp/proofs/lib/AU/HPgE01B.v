(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): part 3 of segment E01 of the
   walk of LLVMFuzzerTestOneInput, 0x80f10 (the target of the size test) -> 0x530e0 (malloc's wrapper, called at
   0x80fc8 with ra = 0x80fcc), lib/AU/HPgE01D.v e01u_body_stmt. Proves no function (kind: segment lemma of
   LLVMFuzzerTestOneInput's walk, one of its four parts).

   THE CODE (lib/AU/HPgE01D.v E01U_TBL):
     0x80f10 .. 0x80f14  sd s5,0x48(s1) (R+0x48 = F); beqz s4 (n = 0: to 0x80f64)
     0x80f18 .. 0x80f24  a0 = p + 1; a1 = 1; bltu a1,a0 (taken: 1 < p + 1; its `j` 0x80f24 to the trap 0x83a14 is
                         in no run)
     0x80f28 .. 0x80f38  lb of the shadow byte s of p at (p >> 3) + K; beqz (s = 0: to 0x80f3c); j 0x83a50
     0x83a50 .. 0x83a58  andi a2,s2,7 (= 0); bge a2,a1 (not taken: 0 < s); j 0x80f3c
     0x80f3c .. 0x80f50  lbu data[0]; R+0x38 = 1 - (data[0] & 1); bne s4,a1 (a1 = 1; n >= 2: to 0x80f78)
     0x80f54 .. 0x80f60  n = 1: s6 = s8 = 0, s2 = p + 1; j 0x80fbc
     0x80f64 .. 0x80f74  n = 0: s6 = s8 = 0, R+0x38 = 1; j 0x80fbc
     0x80f78 .. 0x80f94  n >= 2: a2 = p + 2; bltu a1,a2 (taken; its trap arm 0x80f80 is in no run); lb of the shadow
                         byte of p + 1 (the same cell); beqz; j 0x83ac8
     0x83ac8 .. 0x83ad0  andi a2,a0,7 (= 1); bge a2,a1 (not taken: 1 < s); j 0x80f98
     0x80f98 .. 0x80fb8  lbu data[1]; s6 = n - 2; s2 = p + 2; s8 = data[1] - 10 ((205 data[1]) >> 11) = data[1] mod 10
     0x80fbc .. 0x80fc8  s5 = 0x5000; s4 = a0 = 19744; jal 0x530e0 (ra = 0x80fcc)
   THE RUNS: four engine states from 0x80f10, one per class of the input's length n, each run straight to 0x530e0
   with every branch decided by the state's facts: n = 0 (s4 pinned to 0), n = 1 (s4 pinned to 1, shadow byte 1),
   2 <= n <= 7 (shadow byte n, the atom of s4) and n >= 8 (shadow byte 0). The one written region is the real-frame
   cells [R+0x38, R+0x50) (s1, atom 9; the stack window). For n > 0 there are two read-only regions more: the shadow
   cell of p (the extra atom 32 = (p >> 3) + K, with the aliases of the code's address forms (p >> 3) + K and
   ((p + 1) >> 3) + K, and p & 7 = 0, (p + 1) & 7 = 1) and data[0 .. min(n, 2)) at p (s2, atom 18; the bytes are the
   extra atoms 33 and 34). The facts: 4096 <= p <= 2^47 and 16 | p (the block law), each byte below 256, and n's
   class (atom 20). The shadow byte is the block shadow law's (hm_blk_shadow); the data bytes are the input's
   (hqu_base's garr8 of hu_pl at p, kept by the journal since the input block is live at both ends). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSegM HPgMem HPgE01D.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== arithmetic ======================================== *)
(* the cap byte as the code computes it, data[1] - 10 ((205 data[1]) >> 11), in the engine's arithmetic *)
Definition e01b_capf (x : Z) : Z :=
  zcanon (x - zcanon (zcanon (Z.shiftr (zcanon (x * zcanon 205)) (Z.land (zcanon 11) 63)) * zcanon 10)).
Lemma e01b_capf_ok : forall x, 0 <= x < 256 -> e01b_capf x = x mod 10.
Proof.
intros x Hx.
assert (Hb : forallb (fun i => e01b_capf (Z.of_nat i) =? Z.of_nat i mod 10) (seq 0 256) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat x) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in Hb by lia. apply Z.eqb_eq. exact Hb.
Qed.
(* the not-null word, seqz (data[0] & 1), in the engine's arithmetic *)
Definition e01b_nnf (x : Z) : Z := zcanon (if zcanon (Z.land x (zcanon 1)) <? zcanon 1 then 1 else 0).
Lemma e01b_nnf_ok : forall x, 0 <= x < 256 -> e01b_nnf x = 1 - Z.land x 1.
Proof.
intros x Hx.
assert (Hb : forallb (fun i => e01b_nnf (Z.of_nat i) =? 1 - Z.land (Z.of_nat i) 1) (seq 0 256) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat x) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in Hb by lia. apply Z.eqb_eq. exact Hb.
Qed.
Lemma e01b_land1 : forall x, 0 <= x -> 0 <= Z.land x 1 <= 1.
Proof.
intros x Hx. assert (L : Z.land x 1 = x mod 2) by (apply (Z.land_ones x 1); lia).
rewrite L. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

(* ======================================== the engine's values ======================================== *)
Section sv. Context {fx : YK11.FPState}.
Lemma e01b_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, Z.add_0_r, H, !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma e01b_den_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
intros regs extra n r Hn. apply bv_eq. rewrite denot_SOff, Z.add_0_r, (ew_Ereg_nat regs extra n r Hn).
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.
Lemma e01b_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c H Hv Hc. apply bv_eq. rewrite denot_SOff, H. unfold w64. rewrite !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
(* s8 = data[1] mod 10 *)
Lemma e01b_cap_sv : forall E x, ew E 34 = Z_to_bv 64 x -> 0 <= x < 256 ->
  sv_denot E (SAlu ALU_SUB (SOff 34 0)
    (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff 34 0) (SLit 205)) (SLit 11)) (SLit 10)))
  = Z_to_bv 64 (x mod 10).
Proof.
intros E x H Hx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SMd, U_SAlu, U_SMd, !U_SLit, (U_atom E 34 x H) by lia.
cbn [zalu_raw zmd_raw]. exact (e01b_capf_ok x Hx).
Qed.
(* R+0x38 = 1 - (data[0] & 1) *)
Lemma e01b_nn_sv : forall E x, ew E 33 = Z_to_bv 64 x -> 0 <= x < 256 ->
  sv_denot E (SAlu ALU_SLTU (SAlu ALU_AND (SOff 33 0) (SLit 1)) (SLit 1)) = Z_to_bv 64 (1 - Z.land x 1).
Proof.
intros E x H Hx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SAlu, !U_SLit, (U_atom E 33 x H) by lia.
cbn [zalu_raw]. exact (e01b_nnf_ok x Hx).
Qed.
(* the aliases of the shadow cell's address and of the granule offsets *)
Lemma e01b_ash1 : forall E p, ew E 18 = Z_to_bv 64 p -> ew E 27 = Z_to_bv 64 SHADOW_OFF ->
  ew E 32 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF p) -> 0 <= p < 2 ^ 47 -> p mod 8 = 0 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 1) (SLit 3)) (SOff 27 0)) = sv_denot E (SOff 32 0).
Proof.
intros E p H18 H27 H32 Hp H8. apply U_inj.
assert (Hd : (p + 1) / 8 = p / 8).
{ replace (p + 1) with (1 + (p / 8) * 8) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
  rewrite Z.div_add by lia. change (1 / 8) with 0. lia. }
assert (Hq : 0 <= p / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite U_SAlu, U_SAlu, !U_SOff, U_SLit, H18, H27, H32.
unfold shadow_of_addr, SHADOW_OFF in *.
rewrite !unsigned_lit_small by lia. cbn [zalu_raw].
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold zcanon, M64. rewrite !Z.add_0_r.
rewrite (Z.mod_small (p + 1)) by lia. rewrite Hd. rewrite (Z.mod_small (p / 8)) by lia.
rewrite (Z.mod_small 2147450880) by lia. f_equal. lia.
Qed.
Lemma e01b_and0 : forall E p, ew E 18 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> p mod 8 = 0 ->
  sv_denot E (SAlu ALU_AND (SOff 18 0) (SLit 7)) = sv_denot E (SLit 0).
Proof.
intros E p H18 Hp H8. apply U_inj. rewrite U_SAlu, U_SOff, !U_SLit, H18, unsigned_lit_small by lia.
cbn [zalu_raw]. assert (L7 : Z.land p 7 = p mod 8) by (apply (Z.land_ones p 3); lia).
change (zcanon 7) with 7. rewrite Z.add_0_r, (zcanon_id p) by (unfold M64; lia). rewrite L7, H8. reflexivity.
Qed.
Lemma e01b_and1 : forall E p, ew E 18 = Z_to_bv 64 p -> 0 <= p -> p + 1 < 2 ^ 64 -> p mod 8 = 0 ->
  sv_denot E (SAlu ALU_AND (SOff 18 1) (SLit 7)) = sv_denot E (SLit 1).
Proof.
intros E p H18 H0 H1 H8. apply U_inj. rewrite U_SAlu, U_SOff, !U_SLit, H18, unsigned_lit_small by lia.
cbn [zalu_raw]. assert (L7 : Z.land (p + 1) 7 = (p + 1) mod 8) by (apply (Z.land_ones (p + 1) 3); lia).
assert (M1 : (p + 1) mod 8 = 1) by (rewrite Zplus_mod, H8; reflexivity).
change (zcanon 7) with 7. rewrite (zcanon_id (p + 1)) by (unfold M64; lia). rewrite L7, M1. reflexivity.
Qed.
End sv.

(* ================================ regions, keeps, reading a run's last state ================================ *)
Definition e01b_R38 : YP09.region := YP09.mkRegion (Some 9%nat) 0x38 0x50 0x38 0x50 [].
Definition e01b_sh (v : sv) : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 v)].
Definition e01b_D1 : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition e01b_D2 : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0))].
(* the write window of the runs: the real-frame cells R+0x38 (the not-null word) and R+0x48 (F) *)
Definition e01b_win (R a : Z) : Prop := R + 0x38 <= a < R + 0x50.

Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01b_keep_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Lemma e01b_garr8_keep : forall H H' m m' a l, garr8 rsegs (mrestrict H m) a l ->
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
Lemma e01b_garr8_av : forall H mem a l j, garr8 rsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview rsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof. intros H mem a l j G Hj. destruct (G j Hj) as [V R]. exact (hm_val1_aview rsegs H mem _ _ V R). Qed.
(* an 8-byte cell of the first region of a run's last state *)
Lemma e01b_cell : forall E ss (ms : machine_state) H k lo hi wlo whi cs b off e v,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some k) lo hi wlo whi cs) ->
  bv_unsigned (ew E k) = b -> In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> val_mem rsegs (mrestrict H (ms_mem ms)) (b + off) 8 v.
Proof.
intros E ss ms H k lo hi wlo whi cs b off e v HS Hn Hb Hc He Hv.
pose proof (HPgSteps.st_ok_region_at E ss (restrict H ms) 0 _ HS Hn) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hb in Hck.
exact (val_of_chunk_ok rsegs E _ b off 8 e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
(* the entry regions *)
Lemma e01b_R38_ok : forall E (W : world rsegs) mem R,
  bv_unsigned (ew E 9) = R -> 0 <= R -> R + 0x50 <= 2 ^ 64 ->
  (forall a, R + 0x38 <= a < R + 0x50 -> apresent (w_H W) mem a) ->
  region_ok rsegs E (mrestrict (w_H W) mem) e01b_R38.
Proof.
intros E W mem R H9 H0 H1 HP. unfold e01b_R38.
apply (hm_rw_region rsegs E (w_H W) mem 9 R); [exact H9 | lia | lia | intros o Ho; apply HP; lia | constructor].
Qed.
Lemma e01b_sh_ok : forall E (W : world rsegs) mem sa s v,
  bv_unsigned (ew E 32) = sa -> aview rsegs (w_H W) mem sa = Some s -> sv_denot E v = Z_to_bv 64 s ->
  0 <= sa < 2 ^ 64 -> region_ok rsegs E (mrestrict (w_H W) mem) (e01b_sh v).
Proof.
intros E W mem sa s v H32 A Hv Hsa. unfold e01b_sh.
apply (hm_cell_region rsegs E (w_H W) mem 32 sa s v); [exact H32 | exact A | exact Hv | lia | lia].
Qed.
Lemma e01b_D1_ok : forall E (W : world rsegs) mem p d0,
  bv_unsigned (ew E 18) = p -> ew E 33 = Z_to_bv 64 d0 -> aview rsegs (w_H W) mem p = Some d0 -> 0 <= p < 2 ^ 64 ->
  region_ok rsegs E (mrestrict (w_H W) mem) e01b_D1.
Proof.
intros E W mem p d0 H18 H33 A Hp. unfold e01b_D1.
destruct (hm_aview_val1 rsegs _ _ _ _ A) as [_ R].
apply (hm_cell_region rsegs E (w_H W) mem 18 p d0 (SOff 33 0)); [exact H18 | exact A | | lia | lia].
apply e01b_den_atom; [exact H33 | lia].
Qed.
Lemma e01b_D2_ok : forall E (W : world rsegs) mem p d0 d1,
  bv_unsigned (ew E 18) = p -> ew E 33 = Z_to_bv 64 d0 -> ew E 34 = Z_to_bv 64 d1 ->
  aview rsegs (w_H W) mem p = Some d0 -> aview rsegs (w_H W) mem (p + 1) = Some d1 -> 0 <= p -> p + 2 <= 2 ^ 64 ->
  region_ok rsegs E (mrestrict (w_H W) mem) e01b_D2.
Proof.
intros E W mem p d0 d1 H18 H33 H34 A0 A1 H0 H1. unfold e01b_D2.
destruct (hm_aview_val1 rsegs _ _ _ _ A0) as [V0 R0]. destruct (hm_aview_val1 rsegs _ _ _ _ A1) as [V1 R1].
apply (hm_ro_region rsegs E (w_H W) mem 18 p); [exact H18 | lia | lia |].
constructor; [|constructor; [|constructor]].
- apply (chunk_ok_val rsegs E _ p 0 1%N (SOff 33 0) d0); [apply e01b_den_atom; [exact H33 | lia] | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact V0.
- apply (chunk_ok_val rsegs E _ p 1 1%N (SOff 34 0) d1); [apply e01b_den_atom; [exact H34 | lia] | cbn; lia | cbn; lia |].
  exact V1.
Qed.
(* the three regions of a run with input lie apart: the stack cells, the shadow cell, the input block's bytes *)
Lemma e01b_disj : forall E v cs k R sa p,
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = sa -> bv_unsigned (ew E 18) = p ->
  (R + 0x50 <= sa \/ sa + 1 <= R + 0x38) -> (R + 0x50 <= p \/ p + k <= R + 0x38) -> (sa + 1 <= p \/ p + k <= sa) ->
  pairwise_disjoint E [e01b_R38; e01b_sh v; YP09.mkRegion (Some 18%nat) 0 k 0 0 cs].
Proof.
intros E v cs k R sa p H9 H32 H18 D1 D2 D3. apply pairwise_disjoint_of_extents.
unfold extent_of_region, e01b_R38, e01b_sh.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. rewrite H9, H32, H18.
unfold zdisj. cbn [fst snd]. repeat split; lia.
Qed.
End rd.

(* the facts of the entry states *)
Definition e01b_atoms (f20 : list (nat * afact)) : list (nat * afact) :=
  f20 ++ [(18%nat, mkAF 4096 (2 ^ 47) 4); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)].
Section fa. Context {fx : YK11.FPState}.
Lemma e01b_af : forall E k v lo hi al, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E k (mkAF lo hi al).
Proof.
intros E k v lo hi al H Hv Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H, unsigned_lit_small by lia. split; [exact Hb | split; [exact Hm | exact Ha]].
Qed.
Lemma e01b_atoms_ok : forall E p d0 d1 f20, ew E 18 = Z_to_bv 64 p -> ew E 33 = Z_to_bv 64 d0 ->
  ew E 34 = Z_to_bv 64 d1 -> 4096 <= p <= 2 ^ 47 -> p mod 16 = 0 -> 0 <= d0 < 256 -> 0 <= d1 < 256 ->
  atoms_ok E f20 -> atoms_ok E (e01b_atoms f20).
Proof.
intros E p d0 d1 f20 H18 H33 H34 Hp H16 Hd0 Hd1 Hf. unfold e01b_atoms.
induction f20 as [|[k a] f IH]; cbn [app atoms_ok] in Hf |- *.
- split; [apply (e01b_af E 18 p); [exact H18 | lia | lia | exact H16 | lia]|].
  split; [apply (e01b_af E 33 d0); [exact H33 | lia | lia | apply Z.mod_1_r | lia]|].
  split; [apply (e01b_af E 34 d1); [exact H34 | lia | lia | apply Z.mod_1_r | lia]|].
  exact I.
- destruct Hf as [Ha Hf]. split; [exact Ha | apply IH; exact Hf].
Qed.
End fa.

(* ======================================== the four entry states ======================================== *)
(* the extra atoms: 32 the shadow cell of p, 33 and 34 the input's first two bytes *)
Definition e01b_extra (p d0 d1 : Z) : list word := [w64 (shadow_of_addr SHADOW_OFF p); w64 d0; w64 d1].
Definition e01b_ss (sr : list sv) (rs : smem) (G : facts) : sstate := mkSS E01U_HDR sr rs None G.
(* n = 0 *)
Definition e01b_ss_a : sstate := e01b_ss (sr_set sr_atoms 20%bv (SLit 0)) [e01b_R38] (mkFacts [] [] []).
(* n = 1: the shadow byte of p is 1 *)
Definition e01b_ss_b : sstate := e01b_ss (sr_set sr_atoms 20%bv (SLit 1)) [e01b_R38; e01b_sh (SLit 1); e01b_D1]
  (mkFacts (e01b_atoms []) []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 27 0), SOff 32 0);
     (SAlu ALU_AND (SOff 18 0) (SLit 7), SLit 0)]).
(* 2 <= n <= 7: the shadow byte of p is n *)
Definition e01b_ss_c : sstate := e01b_ss sr_atoms [e01b_R38; e01b_sh (SOff 20 0); e01b_D2]
  (mkFacts (e01b_atoms [(20%nat, mkAF 2 7 0)]) []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 27 0), SOff 32 0);
     (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 1) (SLit 3)) (SOff 27 0), SOff 32 0);
     (SAlu ALU_AND (SOff 18 0) (SLit 7), SLit 0); (SAlu ALU_AND (SOff 18 1) (SLit 7), SLit 1)]).
(* n >= 8: the shadow byte of p is 0 *)
Definition e01b_ss_d : sstate := e01b_ss sr_atoms [e01b_R38; e01b_sh (SLit 0); e01b_D2]
  (mkFacts (e01b_atoms [(20%nat, mkAF 8 (2 ^ 26 - 1) 0)]) []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 27 0), SOff 32 0);
     (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 1) (SLit 3)) (SOff 27 0), SOff 32 0)]).
(* the registers the runs change *)
Definition e01b_clob : list (bv 5) := [1; 10; 11; 12; 18; 20; 21; 22; 24]%bv.
(* the env at the call: the input's cursor and the two harness bytes *)
Definition e01b_env (e : hd_env) (len cap null src left : Z) : hd_env :=
  HDEnv (e_S e) (e_R e) (e_F e) (e_pp e) (e_pod e) (e_out e) (e_first e) len cap null (e_rc e) src left.
(* where the carried cells lie relative to the write window *)
Definition e01b_wb (e : hd_env) : Prop :=
  0 <= e_R e /\ e_R e + 0x50 <= e_S e - 0x88 /\ e_S e <= 2 ^ 47 /\
  0 <= shadow_addr (e_F e) /\ shadow_addr (e_F e) + 116 <= e_R e + 0x38 /\
  0 <= e_F e /\ e_F e + 0x400 <= e_R e + 0x38.

Lemma e01b_r20_nz : (20%bv : bv 5) <> 0%bv.
Proof. intros X. apply (f_equal (@bv_unsigned 5)) in X. cbv in X. discriminate X. Qed.
Lemma e01b_ew32 : forall regs p d0 d1, ew (Ereg regs (e01b_extra p d0 d1)) 32 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF p).
Proof. intros. rewrite (ew_Ereg_extra regs _ 0). reflexivity. Qed.
Lemma e01b_ew33 : forall regs p d0 d1, ew (Ereg regs (e01b_extra p d0 d1)) 33 = Z_to_bv 64 d0.
Proof. intros. rewrite (ew_Ereg_extra regs _ 1). reflexivity. Qed.
Lemma e01b_ew34 : forall regs p d0 d1, ew (Ereg regs (e01b_extra p d0 d1)) 34 = Z_to_bv 64 d1.
Proof. intros. rewrite (ew_Ereg_extra regs _ 2). reflexivity. Qed.

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01b_entry : forall (W : world rsegs) regs mem extra sr rs G,
  regs_ok (Ereg regs extra) sr regs -> regions_wf rs = true ->
  Forall (region_ok rsegs (Ereg regs extra) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (Ereg regs extra) rs -> facts_ok (Ereg regs extra) G ->
  st_ok rsegs (Ereg regs extra) (e01b_ss sr rs G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 E01U_HDR) mem (seg_rom rsegs))).
Proof.
intros W regs mem extra sr rs G Hsr Hwf Hrs Hpd HG. rewrite restrict_mkst_fx. unfold e01b_ss.
apply (entry_st_ok_full rsegs); assumption.
Qed.
End en.

(* ---- tactics of the runs ---- *)
(* the windows of a run lie in e01b_win: the only written region is the real-frame cells *)
Ltac e01b_winT U9 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ rewrite U9 in Ha | idtac ];
      unfold e01b_win; revert Ha; clear; intros Ha; lia | ]);
  destruct Hin.
(* the write windows: the real-frame cells are in the stack window, the other regions read only *)
Ltac e01b_awr U9 R S0 HB0 GS :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; clear; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - S0));
    [ reflexivity | rewrite U9; clear; lia
    | cbn; revert HB0 GS; clear; intros; lia | cbn; revert HB0 GS; clear; intros; lia |] ].
Ltac e01b_nin := let H := fresh "H" in intros H; repeat (destruct H as [H|H]; [discriminate H|]); destruct H.
(* a register of a run's last state, as the engine holds it *)
Ltac e01b_rd HS :=
  lazymatch type of HS with st_ok _ _ ?ssf (restrict ?H ?msf) =>
  rewrite (st_ok_restrict_reg rsegs H _ ssf msf _ HS);
  lazymatch goal with |- sv_denot _ (sr_get (ss_regs ssf) ?r) = _ =>
    let x := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with x end end.
Ltac e01b_kept KR := apply KR; [vm_compute; discriminate | vm_compute; e01b_nin].

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x230 + ASTACK <= LLVMF_STK.
(* the empty input's address (the harness's caller passes it when n = 0) *)
Hypothesis HAE : 0 < A_EMPTY < kLowMemEnd.

(* ---- the input after the two harness bytes, at the call ---- *)
Lemma e01b_in_a : forall (hx : hqu_hcx rsegs) W mem e src,
  hu_pl rsegs hx = [] -> 0 < src < kLowMemEnd ->
  e01u_in B hx W mem (e01b_env e (hd_len []) 0 0 src 0) [].
Proof.
intros hx W mem e src Hpl Hs. unfold e01u_in, hqu_harn. rewrite Hpl. cbn [e01b_env e_src e_left e_len e_cap e_null].
split; [split; [reflexivity | split; [reflexivity | split; [reflexivity | lia]]]|].
split; [reflexivity|]. split; [reflexivity|]. split; [apply garr8_nil|].
split; [lia|]. split; [unfold kLowMemEnd in Hs; lia|].
split; [unfold amem_range, kLowMemEnd in *; lia|]. left; reflexivity.
Qed.
Lemma e01b_in_b : forall (hx : hqu_hcx rsegs) W mem e p b0,
  hu_pl rsegs hx = [b0] -> in_app p 1 -> p + 1 <= 2 ^ 47 ->
  e01u_in B hx W mem (e01b_env e (hd_len []) 0 (Z.land (bv_unsigned b0) 1) (p + 1) 0) [].
Proof.
intros hx W mem e p b0 Hpl Happ H47. unfold e01u_in, hqu_harn. rewrite Hpl.
cbn [e01b_env e_src e_left e_len e_cap e_null].
pose proof (Cursor.byte_range b0) as Rb0. pose proof (e01b_land1 (bv_unsigned b0) ltac:(lia)) as L1.
pose proof ASAN_CEIL_range as AC.
split; [split; [reflexivity | split; [reflexivity | split; [reflexivity | lia]]]|].
split; [reflexivity|]. split; [reflexivity|]. split; [apply garr8_nil|].
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
split; [lia|]. split; [lia|].
split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|]. left; reflexivity.
Qed.
Lemma e01b_in_c : forall (hx : hqu_hcx rsegs) W mem e p n b0 b1 pl,
  hu_pl rsegs hx = b0 :: b1 :: pl -> n = Z.of_nat (length (b0 :: b1 :: pl)) ->
  In (p, n) (ablocks B (hu_ly rsegs hx) (hu_S rsegs hx)) ->
  garr8 rsegs (mrestrict (w_H W) mem) p (hd_zbytes (b0 :: b1 :: pl)) ->
  in_app p n -> p + n <= 2 ^ 47 ->
  e01u_in B hx W mem (e01b_env e (hd_len pl) (bv_unsigned b1 mod 10) (Z.land (bv_unsigned b0) 1) (p + 2) (n - 2)) pl.
Proof.
intros hx W mem e p n b0 b1 pl Hpl Hn Hin G Happ H47. unfold e01u_in, hqu_harn. rewrite Hpl.
cbn [e01b_env e_src e_left e_len e_cap e_null].
pose proof (Cursor.byte_range b0) as Rb0. pose proof (Cursor.byte_range b1) as Rb1.
pose proof (e01b_land1 (bv_unsigned b0) ltac:(lia)) as L1. pose proof (Z.mod_pos_bound (bv_unsigned b1) 10 ltac:(lia)) as M10.
pose proof ASAN_CEIL_range as AC.
cbn [length] in Hn.
split; [split; [reflexivity | split; [reflexivity | split; [reflexivity | lia]]]|].
split; [rewrite Hn; lia|]. split; [reflexivity|].
split.
{ replace (p + 2) with (p + 1 + 1) by lia. apply (e01b_garr8_tl _ _ (bv_unsigned b1)).
  apply (e01b_garr8_tl _ _ (bv_unsigned b0)). exact G. }
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
split; [lia|]. split; [lia|].
split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
right. exists p, n. split; [exact Hin|]. unfold req_size. destruct (Z.eqb_spec n 0); lia.
Qed.

(* ---- the call state from a run's last state ---- *)
Lemma e01b_fin : forall (hx : hqu_hcx rsegs) pos e ly S W regs mem md regs' mem' md' len cap null src left rest,
  e01u_hdr_facts B LLVMF_STK hx pos e ly S W regs mem md ->
  hqu_j rsegs B LLVMF_STK hx [(HQU_CID, pos)] ly S W mem' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ e01b_win (e_R e) a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  e01b_wb e -> 0 <= src -> src + left <= e_R e + 0x38 ->
  getr regs' 1 = w64 E01U_MALLOC_RA ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 23 = getr regs 23 -> getr regs' 27 = getr regs 27 ->
  getr regs' 10 = w64 19744 -> getr regs' 20 = w64 19744 -> getr regs' 21 = w64 0x5000 ->
  getr regs' 18 = w64 src -> getr regs' 22 = w64 left -> getr regs' 24 = w64 cap ->
  val_mem rsegs (mrestrict (w_H W) mem') (e_R e + 0x38) 8 ((1 - null) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) mem') (e_R e + 0x48) 8 (e_F e mod 2 ^ 64) ->
  e01u_in B hx W mem (e01b_env e len cap null src left) rest ->
  e01u_call_facts B LLVMF_STK hx pos (e01b_env e len cap null src left) rest ly S W regs' mem' md'.
Proof.
intros hx pos e ly S W regs mem md regs' mem' md' len cap null src left rest HH HJ' K Wb Hs0 Hsl
  R1 R2 R3 R4 R8 R9 R19 R23 R27 R10 R20 R21 R18 R22 R24 C38 C48 Hin.
destruct HH as (_ & Eab & HG & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G27 & Hfsh & Hkept).
destruct Wb as (WR0 & WRS & WS47 & WSH0 & WSH & WF0 & WFR).
assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= e_R e + 0x38 \/ e_R e + 0x50 <= a) ->
  val_mem rsegs (mrestrict (w_H W) mem) a 8 v -> val_mem rsegs (mrestrict (w_H W) mem') a 8 v).
{ intros a v Ha0 Ha1 Hout V. apply (val_mem_kept rsegs (w_H W) (w_H W) mem mem' a 8 v); [|exact V].
  intros k Hk. cbn in Hk. apply K; [lia | unfold e01b_win; lia]. }
unfold e01u_call_facts.
split; [exact HJ'|]. split; [exact Eab|].
split; [exact (hqu_geo_env rsegs hx pos e (e01b_env e len cap null src left) eq_refl eq_refl eq_refl HG)|].
split; [exact R1|].
split; [cbn [e01b_env e_R]; rewrite R2; exact G2|].
split; [rewrite R3; exact G3|]. split; [rewrite R4; exact G4|].
split; [rewrite R10; reflexivity|].
split.
{ unfold hd_cut. cbn [tl hi_L1 headamp_himg_B].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv e01b_env e_S]; exact (eq_trans R8 G8)|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv e01b_env e_R]; exact (eq_trans R9 G9)|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv e01b_env e_src]; exact R18|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv e01b_env e_F]; exact (eq_trans R19 G19)|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; exact R20|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; exact R21|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv e01b_env e_left]; exact R22|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv e01b_env e_F]; rewrite Z.add_0_r; exact (eq_trans R23 G23)|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv e01b_env e_cap]; exact R24|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv]; exact (eq_trans R27 G27)|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv e01b_env e_R e_null]; exact C38|].
  apply Forall_cons; [cbn [fst snd hd_at hd_xv e01b_env e_R e_F]; rewrite Z.add_0_r; exact C48|].
  apply Forall_nil. }
split.
{ cbn [e01b_env e_F]. apply (hm_fsh_kept rsegs (w_H W) mem (w_H W) mem' (e_F e) headamp_B_shA Hfsh).
  assert (L : length headamp_B_shA = 116%nat) by (vm_compute; reflexivity).
  intros i Hi. rewrite L in Hi. apply K; [lia | unfold e01b_win; lia]. }
split.
{ apply (hqu_kept_env rsegs hx pos e (e01b_env e len cap null src left) W mem' regs' eq_refl eq_refl).
  unfold hqu_kept, hqu_fsaves in Hkept |- *. destruct Hkept as [Hc (v0 & v1 & v2 & v3 & F0 & F1 & F2 & F3)].
  split.
  - rewrite Forall_forall in Hc |- *. intros f Hf. pose proof (Hc f Hf) as Hf'.
    unfold hqu_cells in Hf. apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
    + unfold hqu_saves_L in Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
      cbn [fst snd hd_at hd_xv] in Hf' |- *. apply KV; [lia | lia | lia | exact Hf'].
    + cbn [fst snd hd_at hd_xv] in Hf' |- *. unfold HQU_FLAG in Hf' |- *. apply KV; [lia | lia | lia | exact Hf'].
  - exists v0, v1, v2, v3. cbn [hd_at hd_xv] in F0, F1, F2, F3 |- *.
    split; [apply KV; [lia | lia | lia | exact F0]|].
    split; [apply KV; [lia | lia | lia | exact F1]|].
    split; [apply KV; [lia | lia | lia | exact F2]|].
    apply KV; [lia | lia | lia | exact F3]. }
unfold e01u_in in Hin |- *. destruct Hin as (Hh & Hl & Hlen & G & Hrest).
split; [exact Hh|]. split; [exact Hl|]. split; [exact Hlen|]. split; [|exact Hrest].
apply (e01b_garr8_keep (w_H W) (w_H W) mem mem' _ _ G).
intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj. cbn [e01b_env e_src e_left] in Hl, Hsl, Hs0 |- *.
apply K; [lia | unfold e01b_win; lia].
Qed.

(* ======================================== the part ======================================== *)
Theorem e01u_body_ok : e01u_body_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros hx pos e ly S W regs mem md HB HH.
destruct hx as [ly0 S0 W0 regs0 mem0 md0 p n pl].
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (YM05.alloc_ceiling_val) as Hceilv.
assert (HASTK : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. rewrite HASTK in HSTK'.
pose proof HB as (HPRE & _ & _ & _ & Hpn & Hnl & Hpl & Hfr0 & _).
cbn [hu_ly hu_S hu_W hu_regs hu_mem hu_md hu_p hu_n hu_pl] in HPRE, Hpn, Hnl, Hpl, Hfr0.
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HH as (HJ & Eab & HG & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G23 & G27 & _ & _).
cbn [hu_ly hu_S hu_W hu_regs hu_mem hu_md hu_p hu_n hu_pl] in Eab, G18, G20.
pose proof HG as (GS & GR & GF). cbn [hu_regs hu_ly] in GS, GF. unfold HQU_RSZ in GR.
unfold hqu_j in HJ. cbn [hu_ly hu_S hu_W hu_regs hu_mem hu_md] in HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & HJblk & _ & _ & _ & HJpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (HFly : frame_addr ly HQU_CID pos = e_F e) by (rewrite GF; unfold frame_addr; rewrite HlyF; reflexivity).
assert (Hfin : In (HQU_CID, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ HQU_CID pos HAR Hfin) as (HF4096 & HFceil & _).
rewrite HFly in HF4096, HFceil. change (fs_frame_bytes HQU_CID) with 1024 in HFceil.
(* the geometry: R = 32 ((S - 0x220) / 32), so S - 0x23f <= R <= S - 0x220 *)
assert (HRr : e_S e - 0x23f <= e_R e <= e_S e - 0x220).
{ rewrite GR. pose proof (Z.div_mod (e_S e - 0x220) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (e_S e - 0x220) 32 ltac:(lia)) as M. revert D M. clear. intros. lia. }
assert (HB0 : alloc_ceiling + 0x1000 <= e_R e /\ e_R e + 0x50 <= e_S e - 0x88 /\ e_S e <= 2 ^ 47 /\
  e_S e - LLVMF_STK <= e_R e + 0x38 /\ e_R e + 0x50 <= e_S e).
{ revert HRr GS Hslo Hceil Hshi H47 HSTK' Hstk0. clear. intros. lia. }
assert (HFq : 0 <= e_F e / 8 < 2 ^ 44 - 2 ^ 19).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]]. revert HFceil Hceilv. clear. intros. lia. }
assert (Wb : e01b_wb e).
{ unfold e01b_wb, shadow_addr, SHADOW_OFF. revert HB0 HFq HF4096 HFceil Hceilv. clear. intros. lia. }
assert (U9 : forall extra, bv_unsigned (ew (Ereg regs extra) 9) = e_R e).
{ intros extra. rewrite (ew_Ereg_nat regs extra 9 9%bv eq_refl), G9. unfold w64. apply unsigned_lit_small.
  revert HB0 Hceilv. clear. intros. lia. }
assert (PR38 : forall a, e_R e + 0x38 <= a < e_R e + 0x50 -> apresent (w_H W) mem a).
{ intros a Ha. apply HJpres. rewrite <- GS. revert Ha HB0. clear. intros. lia. }
assert (R38ok : forall extra, region_ok rsegs (Ereg regs extra) (mrestrict (w_H W) mem) e01b_R38).
{ intros extra. apply (e01b_R38_ok _ W mem (e_R e) (U9 extra)); [revert HB0 Hceilv | revert HB0 | exact PR38];
  clear; intros; lia. }
destruct Hpn as [[Hn0 Hpa] | [Hnr Hin]].
{ (* ======== n = 0: the empty input ======== *)
  subst n. destruct pl as [|b0 pl']; [|cbn in Hnl; lia].
  assert (HS : st_ok rsegs (Ereg regs (e01b_extra p 0 0)) e01b_ss_a
    (restrict (w_H W) (mkst regs (Z_to_bv 64 E01U_HDR) mem (seg_rom rsegs)))).
  { apply e01b_entry.
    - apply (regs_ok_pin _ sr_atoms regs 20%bv (SLit 0) (regs_ok_Ereg regs _) e01b_r20_nz). rewrite G20. reflexivity.
    - vm_compute. reflexivity.
    - apply Forall_cons; [apply R38ok | apply Forall_nil].
    - apply pairwise_disjoint_of_extents. cbn. tauto.
    - split; [exact I | split; exact I]. }
  unfold cfg_at. change (w64 E01U_HDR) with (Z_to_bv 64 E01U_HDR).
  aj_run_to E01U_TBL_ok HS HJ E01U_MALLOC. { e01b_awr U9 (e_R e) (spZ regs0) HB0 GS. }
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ e01b_win (e_R e) a ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem a).
  { apply (e01b_keep_frame _ _ (w_H W) mem (ms_mem ms) _ HFr). e01b_winT U9. }
  pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs _ (w_H W) e01b_clob HS (env_agree_refl 32 _)
    ltac:(vm_compute; reflexivity)) as KR.
  apply SRr_ret. unfold e01u_at_call.
  exists pos, (e01b_env e (hd_len []) 0 0 p 0), [], ly, S, (ms_regs ms), (ms_mem ms). eexists.
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
  apply (e01b_fin _ pos e ly S W regs mem md (ms_regs ms) (ms_mem ms) _ (hd_len []) 0 0 p 0 [] HH HJ K Wb).
  - revert HAE Hpa. clear. intros. lia.
  - revert HAE Hpa HB0 Hceilv. clear. unfold kLowMemEnd. intros. lia.
  - e01b_rd HS. reflexivity.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. rewrite (e01b_den_reg regs _ 18 18%bv eq_refl). exact G18.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. reflexivity.
  - eapply (e01b_cell _ _ ms (w_H W) 9 _ _ _ _ _ (e_R e) 56 _ _ HS);
      [reflexivity | exact (U9 _) | cbn; left; reflexivity | reflexivity | apply Z.mod_pos_bound; lia].
  - eapply (e01b_cell _ _ ms (w_H W) 9 _ _ _ _ _ (e_R e) 72 _ _ HS);
      [reflexivity | exact (U9 _) | cbn; right; left; reflexivity | | apply Z.mod_pos_bound; lia].
    rewrite HPgSteps.Z_to_bv_mod64, (e01b_den_reg regs _ 21 21%bv eq_refl). exact G21.
  - apply e01b_in_a; [reflexivity | rewrite Hpa; exact HAE]. }
(* ======== n > 0: the input block (p, n) ======== *)
assert (Hin' : In (p, n) (ablocks B ly S)) by (rewrite Eab; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin') as (Hp16 & Hp4096 & Hpc & Happ & _).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
rewrite Hrq in Hpc, Happ.
assert (Hp8 : p mod 8 = 0).
{ revert Hp16. clear. intros. pose proof (Z.div_mod p 16 ltac:(lia)) as D. rewrite Hp16, Z.add_0_r in D.
  rewrite D. replace (16 * (p / 16)) with ((2 * (p / 16)) * 8) by lia. apply Z_mod_mult. }
assert (Hpq : 0 <= p / 8 < 2 ^ 44 - 2 ^ 19).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]]. revert Hpc Hnr Hceilv. clear. intros. lia. }
assert (Hsa : SHADOW_OFF <= shadow_of_addr SHADOW_OFF p /\ shadow_of_addr SHADOW_OFF p + 1 <= kHighMemBeg).
{ unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg. revert Hpq. clear. intros. lia. }
assert (Hpl' : garr8 rsegs (mrestrict (w_H W) mem) p (hd_zbytes pl)).
{ apply (e01b_garr8_keep (w_H W0) (w_H W) mem0 mem p _ Hpl).
  intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
  apply (HJblk p n (Z.of_nat j) Hin Hin'); [rewrite Hrq; lia | apply inFP_nil]. }
assert (E18 : forall extra, ew (Ereg regs extra) 18 = Z_to_bv 64 p)
  by (intros extra; rewrite (ew_Ereg_nat regs extra 18 18%bv eq_refl); exact G18).
assert (E20 : forall extra, ew (Ereg regs extra) 20 = Z_to_bv 64 n)
  by (intros extra; rewrite (ew_Ereg_nat regs extra 20 20%bv eq_refl); exact G20).
assert (E27 : forall extra, ew (Ereg regs extra) 27 = Z_to_bv 64 SHADOW_OFF)
  by (intros extra; rewrite (ew_Ereg_nat regs extra 27 27%bv eq_refl); exact G27).
assert (U18 : forall extra, bv_unsigned (ew (Ereg regs extra) 18) = p).
{ intros extra. rewrite E18. apply unsigned_lit_small. revert Hp4096 Hpc Hnr Hceilv. clear. intros. lia. }
assert (U32 : forall d0 d1, bv_unsigned (ew (Ereg regs (e01b_extra p d0 d1)) 32) = shadow_of_addr SHADOW_OFF p).
{ intros d0 d1. rewrite e01b_ew32. apply unsigned_lit_small. revert Hsa. clear. unfold SHADOW_OFF, kHighMemBeg. intros. lia. }
assert (Hp64 : 0 <= p < 2 ^ 64) by (revert Hp4096 Hpc Hnr Hceilv; clear; intros; lia).
assert (Hp47 : 0 <= p < 2 ^ 47) by (revert Hp4096 Hpc Hnr Hceilv; clear; intros; lia).
(* the stack cells, the shadow cell and the input bytes lie apart *)
assert (DJ1 : e_R e + 0x50 <= shadow_of_addr SHADOW_OFF p \/ shadow_of_addr SHADOW_OFF p + 1 <= e_R e + 0x38).
{ right. revert Hsa HB0 Hceilv. clear. unfold kHighMemBeg. intros. lia. }
assert (DJ2 : forall k, k <= n -> e_R e + 0x50 <= p \/ p + k <= e_R e + 0x38).
{ intros k Hk. right. revert Hk Hpc HB0 Hceilv. clear. intros. lia. }
assert (DJ3 : forall k, k <= n -> shadow_of_addr SHADOW_OFF p + 1 <= p \/ p + k <= shadow_of_addr SHADOW_OFF p).
{ intros k Hk. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. revert Hk Happ Hsa. clear. unfold SHADOW_OFF, kHighMemBeg.
  intros. lia. }
destruct (Z.eq_dec n 1) as [Hn1 | Hn1].
{ (* ======== n = 1: data[0] only ======== *)
  revert Hnl. subst n. intros Hnl. destruct pl as [|b0 [|b1 pl']]; cbn [length] in Hnl; try lia.
  pose proof (Cursor.byte_range b0) as Rb0.
  assert (A0 : aview rsegs (w_H W) mem p = Some (bv_unsigned b0)).
  { pose proof (e01b_garr8_av _ _ p _ 0 Hpl' ltac:(cbn; lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. exact X. }
  assert (Hs : aview rsegs (w_H W) mem (shadow_of_addr SHADOW_OFF p) = Some 1).
  { pose proof (hm_blk_shadow rsegs B ly S W mem md p 1 0 HAR Hin' ltac:(change ((req_size 1 + 7) / 8) with 1; lia)) as X.
    rewrite Z.add_0_r in X. exact X. }
  assert (HS : st_ok rsegs (Ereg regs (e01b_extra p (bv_unsigned b0) 0)) e01b_ss_b
    (restrict (w_H W) (mkst regs (Z_to_bv 64 E01U_HDR) mem (seg_rom rsegs)))).
  { apply e01b_entry.
    - apply (regs_ok_pin _ sr_atoms regs 20%bv (SLit 1) (regs_ok_Ereg regs _) e01b_r20_nz). rewrite G20. reflexivity.
    - vm_compute. reflexivity.
    - apply Forall_cons; [apply R38ok|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (e01b_sh_ok _ W mem (shadow_of_addr SHADOW_OFF p) 1 (SLit 1) (U32 _ _) Hs); [reflexivity|].
        revert Hsa. clear. unfold SHADOW_OFF, kHighMemBeg. intros. lia.
      + apply (e01b_D1_ok _ W mem p (bv_unsigned b0) (U18 _) (e01b_ew33 _ _ _ _) A0 Hp64).
    - apply (e01b_disj _ _ _ 1 (e_R e) (shadow_of_addr SHADOW_OFF p) p (U9 _) (U32 _ _) (U18 _) DJ1 (DJ2 1 ltac:(lia))
        (DJ3 1 ltac:(lia))).
    - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
      split; [apply (e01b_atoms_ok _ p (bv_unsigned b0) 0 []); [exact (E18 _) | exact (e01b_ew33 _ _ _ _)
        | exact (e01b_ew34 _ _ _ _) | revert Hp4096 Hp47; clear; intros; lia | exact Hp16 | exact Rb0 | lia | exact I]|].
      split; [exact I|].
      split; [exact (shadow_decl_ok _ 18 27 32 p SHADOW_OFF (E18 _) Hp64 (E27 _) (e01b_ew32 _ _ _ _))|].
      split; [exact (e01b_and0 _ p (E18 _) Hp64 Hp8) | exact I]. }
  unfold cfg_at. change (w64 E01U_HDR) with (Z_to_bv 64 E01U_HDR).
  aj_run_to E01U_TBL_ok HS HJ E01U_MALLOC. { e01b_awr U9 (e_R e) (spZ regs0) HB0 GS. }
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ e01b_win (e_R e) a ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem a).
  { apply (e01b_keep_frame _ _ (w_H W) mem (ms_mem ms) _ HFr). e01b_winT U9. }
  pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs _ (w_H W) e01b_clob HS (env_agree_refl 32 _)
    ltac:(vm_compute; reflexivity)) as KR.
  apply SRr_ret. unfold e01u_at_call.
  exists pos, (e01b_env e (hd_len []) 0 (Z.land (bv_unsigned b0) 1) (p + 1) 0), [], ly, S, (ms_regs ms), (ms_mem ms).
  eexists.
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
  apply (e01b_fin _ pos e ly S W regs mem md (ms_regs ms) (ms_mem ms) _ (hd_len []) 0 (Z.land (bv_unsigned b0) 1)
    (p + 1) 0 [] HH HJ K Wb).
  - lia.
  - revert Hpc HB0. clear. intros. lia.
  - e01b_rd HS. reflexivity.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. apply (e01b_den_off _ 18 p 1 (E18 _)); revert Hp47; clear; intros; lia.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. reflexivity.
  - eapply (e01b_cell _ _ ms (w_H W) 9 _ _ _ _ _ (e_R e) 56 _ _ HS);
      [reflexivity | exact (U9 _) | cbn; left; reflexivity | | apply Z.mod_pos_bound; lia].
    rewrite HPgSteps.Z_to_bv_mod64. exact (e01b_nn_sv _ (bv_unsigned b0) (e01b_ew33 _ _ _ _) Rb0).
  - eapply (e01b_cell _ _ ms (w_H W) 9 _ _ _ _ _ (e_R e) 72 _ _ HS);
      [reflexivity | exact (U9 _) | cbn; right; left; reflexivity | | apply Z.mod_pos_bound; lia].
    rewrite HPgSteps.Z_to_bv_mod64, (e01b_den_reg regs _ 21 21%bv eq_refl). exact G21.
  - apply (e01b_in_b _ W mem e p b0); [reflexivity | exact Happ | revert Hp47 Hpc Hceilv; clear; intros; lia]. }
(* ======== n >= 2: data[0] and data[1] ======== *)
destruct pl as [|b0 [|b1 pl']]; cbn [length] in Hnl; [lia | lia |].
pose proof (Cursor.byte_range b0) as Rb0. pose proof (Cursor.byte_range b1) as Rb1.
assert (A0 : aview rsegs (w_H W) mem p = Some (bv_unsigned b0)).
{ pose proof (e01b_garr8_av _ _ p _ 0 Hpl' ltac:(cbn; lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. exact X. }
assert (A1 : aview rsegs (w_H W) mem (p + 1) = Some (bv_unsigned b1)).
{ pose proof (e01b_garr8_av _ _ p _ 1 Hpl' ltac:(cbn; lia)) as X. cbn [Z.of_nat] in X. exact X. }
assert (Hn2 : 2 <= n) by lia.
destruct (Z_lt_le_dec n 8) as [Hn8 | Hn8].
{ (* ======== 2 <= n <= 7: the shadow byte of p is n ======== *)
  assert (Hs : aview rsegs (w_H W) mem (shadow_of_addr SHADOW_OFF p) = Some n).
  { pose proof (hm_blk_shadow rsegs B ly S W mem md p n 0 HAR Hin'
      ltac:(rewrite Hrq; split; [lia | apply Z.div_str_pos; lia])) as X.
    rewrite Z.add_0_r, Hrq in X. rewrite (Z.div_small n 8) in X by lia. rewrite (Z.mod_small n 8) in X by lia.
    exact X. }
  assert (HS : st_ok rsegs (Ereg regs (e01b_extra p (bv_unsigned b0) (bv_unsigned b1))) e01b_ss_c
    (restrict (w_H W) (mkst regs (Z_to_bv 64 E01U_HDR) mem (seg_rom rsegs)))).
  { apply e01b_entry.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [apply R38ok|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (e01b_sh_ok _ W mem (shadow_of_addr SHADOW_OFF p) n (SOff 20 0) (U32 _ _) Hs).
        * apply e01b_den_atom; [exact (E20 _) | lia].
        * revert Hsa. clear. unfold SHADOW_OFF, kHighMemBeg. intros. lia.
      + apply (e01b_D2_ok _ W mem p (bv_unsigned b0) (bv_unsigned b1) (U18 _) (e01b_ew33 _ _ _ _)
          (e01b_ew34 _ _ _ _) A0 A1); revert Hp64 Hp47; clear; intros; lia.
    - apply (e01b_disj _ _ _ 2 (e_R e) (shadow_of_addr SHADOW_OFF p) p (U9 _) (U32 _ _) (U18 _) DJ1 (DJ2 2 Hn2)
        (DJ3 2 Hn2)).
    - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
      split.
      { apply (e01b_atoms_ok _ p (bv_unsigned b0) (bv_unsigned b1)); [exact (E18 _) | exact (e01b_ew33 _ _ _ _)
          | exact (e01b_ew34 _ _ _ _) | revert Hp4096 Hp47; clear; intros; lia | exact Hp16 | exact Rb0 | exact Rb1 |].
        cbn [atoms_ok]. split; [|exact I]. apply (e01b_af _ 20 n); [exact (E20 _) | lia | lia | apply Z.mod_1_r | lia]. }
      split; [exact I|].
      split; [exact (shadow_decl_ok _ 18 27 32 p SHADOW_OFF (E18 _) Hp64 (E27 _) (e01b_ew32 _ _ _ _))|].
      split; [exact (e01b_ash1 _ p (E18 _) (E27 _) (e01b_ew32 _ _ _ _) Hp47 Hp8)|].
      split; [exact (e01b_and0 _ p (E18 _) Hp64 Hp8)|].
      split; [apply (e01b_and1 _ p (E18 _)); revert Hp47 Hp8; clear; intros; lia | exact I]. }
  unfold cfg_at. change (w64 E01U_HDR) with (Z_to_bv 64 E01U_HDR).
  aj_run_to E01U_TBL_ok HS HJ E01U_MALLOC. { e01b_awr U9 (e_R e) (spZ regs0) HB0 GS. }
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ e01b_win (e_R e) a ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem a).
  { apply (e01b_keep_frame _ _ (w_H W) mem (ms_mem ms) _ HFr). e01b_winT U9. }
  pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs _ (w_H W) e01b_clob HS (env_agree_refl 32 _)
    ltac:(vm_compute; reflexivity)) as KR.
  apply SRr_ret. unfold e01u_at_call.
  exists pos, (e01b_env e (hd_len pl') (bv_unsigned b1 mod 10) (Z.land (bv_unsigned b0) 1) (p + 2) (n - 2)), pl', ly, S,
    (ms_regs ms), (ms_mem ms).
  eexists.
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
  apply (e01b_fin _ pos e ly S W regs mem md (ms_regs ms) (ms_mem ms) _ (hd_len pl') (bv_unsigned b1 mod 10)
    (Z.land (bv_unsigned b0) 1) (p + 2) (n - 2) pl' HH HJ K Wb).
  - lia.
  - revert Hpc HB0. clear. intros. lia.
  - e01b_rd HS. reflexivity.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_kept KR.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. reflexivity.
  - e01b_rd HS. apply (e01b_den_off _ 18 p 2 (E18 _)); revert Hp47; clear; intros; lia.
  - e01b_rd HS. replace (n - 2) with (n + -2) by lia. apply (e01b_den_off _ 20 n (-2) (E20 _)); lia.
  - e01b_rd HS. exact (e01b_cap_sv _ (bv_unsigned b1) (e01b_ew34 _ _ _ _) Rb1).
  - eapply (e01b_cell _ _ ms (w_H W) 9 _ _ _ _ _ (e_R e) 56 _ _ HS);
      [reflexivity | exact (U9 _) | cbn; left; reflexivity | | apply Z.mod_pos_bound; lia].
    rewrite HPgSteps.Z_to_bv_mod64. exact (e01b_nn_sv _ (bv_unsigned b0) (e01b_ew33 _ _ _ _) Rb0).
  - eapply (e01b_cell _ _ ms (w_H W) 9 _ _ _ _ _ (e_R e) 72 _ _ HS);
      [reflexivity | exact (U9 _) | cbn; right; left; reflexivity | | apply Z.mod_pos_bound; lia].
    rewrite HPgSteps.Z_to_bv_mod64, (e01b_den_reg regs _ 21 21%bv eq_refl). exact G21.
  - apply (e01b_in_c _ W mem e p n b0 b1 pl');
    [reflexivity | exact Hnl | exact Hin | exact Hpl' | exact Happ | revert Hp47 Hpc Hceilv; clear; intros; lia]. }
(* ======== n >= 8: the shadow byte of p is 0 ======== *)
assert (Hs : aview rsegs (w_H W) mem (shadow_of_addr SHADOW_OFF p) = Some 0).
{ pose proof (hm_blk_shadow rsegs B ly S W mem md p n 0 HAR Hin'
    ltac:(rewrite Hrq; split; [lia | apply Z.div_str_pos; lia])) as X.
  rewrite Z.add_0_r, Hrq in X.
  replace (0 <? n / 8) with true in X by (symmetry; apply Z.ltb_lt; apply Z.div_str_pos; lia).
  exact X. }
assert (HS : st_ok rsegs (Ereg regs (e01b_extra p (bv_unsigned b0) (bv_unsigned b1))) e01b_ss_d
  (restrict (w_H W) (mkst regs (Z_to_bv 64 E01U_HDR) mem (seg_rom rsegs)))).
{ apply e01b_entry.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [apply R38ok|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (e01b_sh_ok _ W mem (shadow_of_addr SHADOW_OFF p) 0 (SLit 0) (U32 _ _) Hs); [reflexivity|].
      revert Hsa. clear. unfold SHADOW_OFF, kHighMemBeg. intros. lia.
    + apply (e01b_D2_ok _ W mem p (bv_unsigned b0) (bv_unsigned b1) (U18 _) (e01b_ew33 _ _ _ _)
        (e01b_ew34 _ _ _ _) A0 A1); revert Hp64 Hp47; clear; intros; lia.
  - apply (e01b_disj _ _ _ 2 (e_R e) (shadow_of_addr SHADOW_OFF p) p (U9 _) (U32 _ _) (U18 _) DJ1 (DJ2 2 Hn2)
      (DJ3 2 Hn2)).
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    split.
    { apply (e01b_atoms_ok _ p (bv_unsigned b0) (bv_unsigned b1)); [exact (E18 _) | exact (e01b_ew33 _ _ _ _)
        | exact (e01b_ew34 _ _ _ _) | revert Hp4096 Hp47; clear; intros; lia | exact Hp16 | exact Rb0 | exact Rb1 |].
      cbn [atoms_ok]. split; [|exact I]. apply (e01b_af _ 20 n); [exact (E20 _) | lia | lia | apply Z.mod_1_r | lia]. }
    split; [exact I|].
    split; [exact (shadow_decl_ok _ 18 27 32 p SHADOW_OFF (E18 _) Hp64 (E27 _) (e01b_ew32 _ _ _ _))|].
    split; [exact (e01b_ash1 _ p (E18 _) (E27 _) (e01b_ew32 _ _ _ _) Hp47 Hp8) | exact I]. }
unfold cfg_at. change (w64 E01U_HDR) with (Z_to_bv 64 E01U_HDR).
aj_run_to E01U_TBL_ok HS HJ E01U_MALLOC. { e01b_awr U9 (e_R e) (spZ regs0) HB0 GS. }
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ e01b_win (e_R e) a ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem a).
{ apply (e01b_keep_frame _ _ (w_H W) mem (ms_mem ms) _ HFr). e01b_winT U9. }
pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs _ (w_H W) e01b_clob HS (env_agree_refl 32 _)
  ltac:(vm_compute; reflexivity)) as KR.
apply SRr_ret. unfold e01u_at_call.
exists pos, (e01b_env e (hd_len pl') (bv_unsigned b1 mod 10) (Z.land (bv_unsigned b0) 1) (p + 2) (n - 2)), pl', ly, S,
  (ms_regs ms), (ms_mem ms).
eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
apply (e01b_fin _ pos e ly S W regs mem md (ms_regs ms) (ms_mem ms) _ (hd_len pl') (bv_unsigned b1 mod 10)
  (Z.land (bv_unsigned b0) 1) (p + 2) (n - 2) pl' HH HJ K Wb).
- lia.
- revert Hpc HB0. clear. intros. lia.
- e01b_rd HS. reflexivity.
- e01b_kept KR.
- e01b_kept KR.
- e01b_kept KR.
- e01b_kept KR.
- e01b_kept KR.
- e01b_kept KR.
- e01b_kept KR.
- e01b_kept KR.
- e01b_rd HS. reflexivity.
- e01b_rd HS. reflexivity.
- e01b_rd HS. reflexivity.
- e01b_rd HS. apply (e01b_den_off _ 18 p 2 (E18 _)); revert Hp47; clear; intros; lia.
- e01b_rd HS. replace (n - 2) with (n + -2) by lia. apply (e01b_den_off _ 20 n (-2) (E20 _)); lia.
- e01b_rd HS. exact (e01b_cap_sv _ (bv_unsigned b1) (e01b_ew34 _ _ _ _) Rb1).
- eapply (e01b_cell _ _ ms (w_H W) 9 _ _ _ _ _ (e_R e) 56 _ _ HS);
    [reflexivity | exact (U9 _) | cbn; left; reflexivity | | apply Z.mod_pos_bound; lia].
  rewrite HPgSteps.Z_to_bv_mod64. exact (e01b_nn_sv _ (bv_unsigned b0) (e01b_ew33 _ _ _ _) Rb0).
- eapply (e01b_cell _ _ ms (w_H W) 9 _ _ _ _ _ (e_R e) 72 _ _ HS);
    [reflexivity | exact (U9 _) | cbn; right; left; reflexivity | | apply Z.mod_pos_bound; lia].
  rewrite HPgSteps.Z_to_bv_mod64, (e01b_den_reg regs _ 21 21%bv eq_refl). exact G21.
- apply (e01b_in_c _ W mem e p n b0 b1 pl');
    [reflexivity | exact Hnl | exact Hin | exact Hpl' | exact Happ | revert Hp47 Hpc Hceilv; clear; intros; lia].
Qed.
Print Assumptions e01u_body_ok.
End p.

Print Assumptions e01u_body_ok.
About e01u_body_ok.
