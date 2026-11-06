(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the block statement
   w6c_case7_stmt of lib/A/RPgW6cBase.v, case 7 of ent_build's `switch (kind % 10)` (pod.h:351-358) inside
   LLVMFuzzerTestOneInput 0x7ff88, from the case entry 0x80f64 to the join J 0x8165c. Proves no function (kind:
   segment lemma): the callee of the copy is the Section hypothesis AMEMCPY.

   THE CODE (registers as in lib/A/RPgW6cEng.v: s1 = R, s7 = SHADOW_OFF, s8 = the cursor, s9 = |r|, a4 = cursor - 1):
     0x80f64  beqz s9 -> 0x81254                           no byte left
     0x80f68 .. 0x80f74  the shadow check of s8 (slow block 0x819fc)
     0x80f78  a1 := [s8] (t); s8 := a4 + 2; a1 := t % 21 (the 0x87 multiply); a2 := [R+0xf0];
              sw a1,0(a2) (e.type); s4 := [R+0xb0]; a1 := [R+0xf8]; bne a1,2 -> 0x8148c
     0x80fcc  a1 := 0; a2 := 0; j 0x814c8                  exactly one byte left
     0x81254  a1 := 0; a2 := 0; s4 := [R+0xb0]; j 0x814c8  no byte left (e.type is never written: it stays 0)
     0x8148c .. 0x81498  the shadow check of s8 (slow block 0x81a70)
     0x8149c  a2 := [s8] (s); a1 := [R+0xf8] - 3; s8 := a4 + 3; a2 := s % 12 (the 0x15555556 multiply)
     0x814c8  a0 := [R+0xf0]; sw a2,4(a0) (e.size); bltu a2,a1 -> 0x81514
     0x814d4  a2 := a1
     0x81514  s9 := s8 + a2; a1 := a1 - a2; sd a1,0xf8(s1); a0 := [R+0xc0] (e.body); a1 := s8;
              0x81528 jal __asan_memcpy (0x510d4)
   THE PROOF is cut by the length of the input after the kind byte, with the entry state of lib/A/RPgW6cEng.v:
     r = []            regions RS, RE, N = 1, s9 pinned to the literal 0: one engine run;
     r = [t]           regions RS, RE, RI 1, N = 2: one run to `bne a1,2` 0x80fc8, whose taken arm contradicts
                       [R+0xf8] = 2, then one run;
     r = t :: s :: r'  regions RS, RE, RI 2, N in [3, 2 ^ 47]: one run to `bltu a2,a1` 0x814d0, which the engine
                       cannot decide, then one run per arm (srr_branch_tok).
   Every run ends at the callee's entry 0x510d4, where lib/A/RPgW6cTail.v's w6c_tail_cpy takes the call and the
   `j J` after it; w6c_jpost_trans re-seats its post on the case entry's state. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSteps RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW6cTail RPgW6cEng RPgW6cBase RPgW6c7A.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================== the model of case 7 at the three input lengths ===================== *)
Lemma w6c7_kind : Z.to_nat (bv_unsigned (Z_to_bv 8 7) mod 10) = 7%nat.
Proof. reflexivity. Qed.

Lemma w6c7_ent0 : w6c_ent 7 [] = (Ent 0 0 [], []).
Proof.
unfold w6c_ent, ent_build. cbv beta iota zeta delta [Cursor.fuzz_u8].
rewrite w6c7_kind. cbv beta iota zeta delta [Cursor.fuzz_u8 Cursor.fuzz_take]. reflexivity.
Qed.

Lemma w6c7_ent1 : forall t0 : byte, w6c_ent 7 [t0] = (Ent (bv_unsigned t0 mod 21) 0 [], []).
Proof.
intros t0. unfold w6c_ent, ent_build. cbv beta iota zeta delta [Cursor.fuzz_u8].
rewrite w6c7_kind. cbv beta iota zeta delta [Cursor.fuzz_u8 Cursor.fuzz_take]. reflexivity.
Qed.

Lemma w6c7_ent2 : forall (t0 s0 : byte) (rest : list byte),
w6c_ent 7 (t0 :: s0 :: rest) =
(Ent (bv_unsigned t0 mod 21) (bv_unsigned s0 mod 12)
   (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest
    ++ zeros (Z.to_nat (bv_unsigned s0 mod 12) - length (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest))),
 skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest).
Proof.
intros t0 s0 rest. unfold w6c_ent, ent_build. cbv beta iota zeta delta [Cursor.fuzz_u8].
rewrite w6c7_kind. cbv beta iota zeta delta [Cursor.fuzz_u8 Cursor.fuzz_take]. reflexivity.
Qed.

(* ===================== the write windows of every state this file runs ===================== *)
(* every region of every state writes only inside [R+0xf8, R+0x100) (atom 9) or [F+0xf0, F+0xf8) (atom 32) *)
Definition w6c7_wok (r : YP09.region) : bool :=
(YP09.r_whi r <=? YP09.r_wlo r)
|| match YP09.r_base r with
   | Some n =>
     (Nat.eqb n 9 && (0xf8 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0x100))
     || (Nat.eqb n 32 && (0xf0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0xf8))
   | None => false
   end.

Lemma w6c7_wr_in : forall E (rs : smem) R F a,
bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> forallb w6c7_wok rs = true ->
in_wrange E rs a -> (R + 0xf8 <= a < R + 0x100) \/ (F + 0xf0 <= a < F + 0xf8).
Proof.
intros E rs R F a U9 U32 Hall (r & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hall r Hin) as Hw. unfold w6c7_wok in Hw.
apply orb_prop in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
destruct (YP09.r_base r) as [nb|] eqn:Hb; [|discriminate Hw].
rewrite ?Hb in Hr. cbn [base_val] in Hr.
apply orb_prop in Hw as [Hw|Hw]; apply andb_prop in Hw as [Hw Hhi]; apply andb_prop in Hw as [Hn Hlo];
apply Nat.eqb_eq in Hn; subst nb; apply Z.leb_le in Hlo; apply Z.leb_le in Hhi.
- rewrite U9 in Hr. left. lia.
- rewrite U32 in Hr. right. lia.
Qed.

Lemma w6c7_awr_ok : forall E (rs : smem) R F STK sp0 FP bl0 blc ly own,
bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> forallb w6c7_wok rs = true ->
sp0 - STK <= R - 16384 -> R + 0x1a0 <= sp0 ->
(forall a, F <= a < F + 512 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs R F STK sp0 FP bl0 blc ly own U9 U32 Hall HS1 HS2 HFw a Ha.
destruct (w6c7_wr_in E rs R F a U9 U32 Hall Ha) as [H|H]; [left; lia | apply HFw; lia].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma w6c7_keep1 : forall E (rs : smem) R F (m0 m1 m2 : word -> option byte) (W : world rsegs),
(forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (F + 0xf0 <= a < F + 0xf8) ->
 aview rsegs (w_H W) m1 a = aview rsegs (w_H W) m0 a) ->
frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
forallb w6c7_wok rs = true -> bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (F + 0xf0 <= a < F + 0xf8) ->
 aview rsegs (w_H W) m2 a = aview rsegs (w_H W) m0 a).
Proof.
intros E rs R F m0 m1 m2 W HK HF Hall U9 U32 a Ha H1 H2.
rewrite <- (HK a Ha H1 H2). apply (aview_eq_of rsegs). apply HF.
rewrite unsigned_lit_small by exact Ha.
intros X. destruct (w6c7_wr_in E rs R F a U9 U32 Hall X) as [Y|Y]; [exact (H1 Y) | exact (H2 Y)].
Qed.

(* ===================== the shadow band is outside the two write windows ===================== *)
Lemma w6c7_shadow_eq : forall (W : world rsegs) (m0 m1 : word -> option byte) R F,
(forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (F + 0xf0 <= a < F + 0xf8) ->
 aview rsegs (w_H W) m1 a = aview rsegs (w_H W) m0 a) ->
kHighMemBeg <= R - T_SEG_STK -> in_app F 512 ->
forall x, SHADOW_OFF - 8 <= x < SHADOW_OFF + 2 ^ 44 + 64 ->
aview rsegs (w_H W) m1 x = aview rsegs (w_H W) m0 x.
Proof.
intros W m0 m1 R F HK HR HFa x Hx.
destruct HFa as (HF0 & [HF1 | [HF1 HF2]]);
apply HK; unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, T_SEG_STK, ASTACK in *; lia.
Qed.

Lemma w6c7_ra_tr : forall (W : world rsegs) (m0 m1 : word -> option byte) a n,
range_addressable (aview rsegs (w_H W) m0) SHADOW_OFF a n ->
(forall x, SHADOW_OFF - 8 <= x < SHADOW_OFF + 2 ^ 44 + 64 -> aview rsegs (w_H W) m1 x = aview rsegs (w_H W) m0 x) ->
0 <= a -> a + n <= 2 ^ 47 ->
range_addressable (aview rsegs (w_H W) m1) SHADOW_OFF a n.
Proof.
intros W m0 m1 a n HR HK Ha Han x Hx. destruct (HR x Hx) as (sv & Hs & Hok).
exists sv. split; [|exact Hok]. rewrite <- Hs. apply HK.
unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma w6c7_hull_tr : forall (W : world rsegs) (m0 m1 : word -> option byte) a n,
shadow_hull_vis (aview rsegs (w_H W) m0) a n ->
(forall x, SHADOW_OFF - 8 <= x < SHADOW_OFF + 2 ^ 44 + 64 -> aview rsegs (w_H W) m1 x = aview rsegs (w_H W) m0 x) ->
0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
shadow_hull_vis (aview rsegs (w_H W) m1) a n.
Proof.
intros W m0 m1 a n HH HK Ha Han Hn s Hs.
rewrite HK; [apply HH; exact Hs|].
assert (HA : SHADOW_OFF <= shadow_addr a).
{ unfold shadow_addr. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). lia. }
assert (HBv : shadow_addr (a + n - 1) <= SHADOW_OFF + 2 ^ 44).
{ unfold shadow_addr. pose proof (Z.div_lt_upper_bound (a + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (shadow_addr (a + n - 1)) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (shadow_addr (a + n - 1)) 8 ltac:(lia)) as M2.
unfold shadow_hull_vis in Hs. unfold SHADOW_OFF in *. lia.
Qed.

Lemma w6c7_fsh_tr : forall (W : world rsegs) (m0 m1 : word -> option byte) F pat,
rl_fsh rsegs (w_H W) m0 F pat ->
(forall x, SHADOW_OFF - 8 <= x < SHADOW_OFF + 2 ^ 44 + 64 -> aview rsegs (w_H W) m1 x = aview rsegs (w_H W) m0 x) ->
0 <= F -> F < 2 ^ 47 -> Z.of_nat (length pat) <= 64 ->
rl_fsh rsegs (w_H W) m1 F pat.
Proof.
intros W m0 m1 F pat HP HK HF0 HF1 Hlen i Hi.
rewrite HK; [apply HP; exact Hi|].
unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.
End b.

(* ===================== reading the final symbolic state ===================== *)
Lemma w6c7_soff : forall (E : env) (n : nat) v c, ew E n = Z_to_bv 64 v ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H Hv Hc. apply bv_eq.
rewrite denot_SOff, H, (unsigned_lit_small v Hv), (unsigned_lit_small (v + c) Hc).
apply zcanon_id. unfold M64. lia.
Qed.

Lemma w6c7_add : forall (E : env) a b va vb, sv_denot E a = Z_to_bv 64 va -> sv_denot E b = Z_to_bv 64 vb ->
0 <= va < 2 ^ 64 -> 0 <= vb < 2 ^ 64 -> 0 <= va + vb < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD a b) = Z_to_bv 64 (va + vb).
Proof.
intros E a b va vb Ha Hb Hva Hvb Hr. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD a b))) with (U E (SAlu ALU_ADD a b)).
rewrite U_SAlu. unfold U. rewrite Ha, Hb, (unsigned_lit_small va Hva), (unsigned_lit_small vb Hvb).
cbn [zalu_raw]. rewrite (unsigned_lit_small (va + vb) Hr). apply zcanon_id. unfold M64. lia.
Qed.

Lemma w6c7_sub : forall (E : env) a b va vb, sv_denot E a = Z_to_bv 64 va -> sv_denot E b = Z_to_bv 64 vb ->
0 <= va < 2 ^ 64 -> 0 <= vb < 2 ^ 64 -> 0 <= va - vb < 2 ^ 64 ->
sv_denot E (SAlu ALU_SUB a b) = Z_to_bv 64 (va - vb).
Proof.
intros E a b va vb Ha Hb Hva Hvb Hr. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_SUB a b))) with (U E (SAlu ALU_SUB a b)).
rewrite U_SAlu. unfold U. rewrite Ha, Hb, (unsigned_lit_small va Hva), (unsigned_lit_small vb Hvb).
cbn [zalu_raw]. rewrite (unsigned_lit_small (va - vb) Hr). apply zcanon_id. unfold M64. lia.
Qed.

Lemma w6c7_chunk : forall {fx : YK11.FPState} E ss ms (H : word -> bool) i rg off (w : N) e v (nb : nat) b,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some rg ->
YP09.r_base rg = Some nb -> In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks rg) ->
bv_unsigned (ew E nb) = b -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
val_mem rsegs (mrestrict H (ms_mem ms)) (b + off) (N.to_nat w) v.
Proof.
intros fx E ss ms H i rg off w e v nb b HS Hi Hb Hc Hnb He Hv Hw.
pose proof (w6c_region_nth E ss (restrict H ms) i rg HS Hi) as HRg.
destruct rg as [bse lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_chunks] in Hb, Hc. rewrite Hb in HRg.
exact (w6c_field E _ nb b cs lo hi wlo whi off w e v HRg Hnb Hc He Hv Hw).
Qed.
Lemma w6c7_w4 : forall v, 0 <= v < 2 ^ 32 -> 0 <= v < 2 ^ (8 * Z.of_N 4).
Proof. intros v H. exact H. Qed.
Lemma w6c7_w8 : forall v, 0 <= v < 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N 8).
Proof. intros v H. exact H. Qed.

(* the branch `bltu a2,a1` 0x814d0: a2 = s % 12, a1 = [R+0xf8] - 3 *)
Lemma w6c7_ltu : forall (E : env) s M, ew E 36 = Z_to_bv 64 s -> 0 <= s < 256 ->
ew E 33 = Z_to_bv 64 (M + 3) -> 0 <= M -> M + 3 < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E w6c_e7s) (sv_denot E (SOff 33 (-3))) = (s mod 12 <? M).
Proof.
intros E s M E36 Hs E33 HM0 HM1. pose proof (Z.mod_pos_bound s 12 ltac:(lia)).
rewrite branch_ltu_U. unfold U.
rewrite (w6c_s12 E s E36 Hs), (w6c7_soff E 33 (M + 3) (-3) E33 ltac:(lia) ltac:(lia)).
rewrite (unsigned_lit_small (s mod 12) ltac:(lia)), (unsigned_lit_small (M + 3 + -3) ltac:(lia)).
f_equal. lia.
Qed.

Lemma w6c7_ltu_t : forall (E : env) s M, ew E 36 = Z_to_bv 64 s -> 0 <= s < 256 ->
ew E 33 = Z_to_bv 64 (M + 3) -> 0 <= M -> M + 3 < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E w6c_e7s) (sv_denot E (SOff 33 (-3))) = true -> s mod 12 < M.
Proof.
intros E s M A1 A2 A3 A4 A5 Hc. rewrite (w6c7_ltu E s M A1 A2 A3 A4 A5) in Hc. apply Z.ltb_lt. exact Hc.
Qed.

Lemma w6c7_ltu_f : forall (E : env) s M, ew E 36 = Z_to_bv 64 s -> 0 <= s < 256 ->
ew E 33 = Z_to_bv 64 (M + 3) -> 0 <= M -> M + 3 < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E w6c_e7s) (sv_denot E (SOff 33 (-3))) = false -> M <= s mod 12.
Proof.
intros E s M A1 A2 A3 A4 A5 Hc. rewrite (w6c7_ltu E s M A1 A2 A3 A4 A5) in Hc. apply Z.ltb_ge. exact Hc.
Qed.

(* the branch `bne a1,a2` 0x80fc8 with [R+0xf8] = 2: its taken arm is impossible *)
Lemma w6c7_ne2 : forall (E : env), ew E 33 = Z_to_bv 64 2 ->
branch_taken BC_NE (sv_denot E (SOff 33 0)) (sv_denot E (SLit 2)) = true -> False.
Proof.
intros E E33 Hc. rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
rewrite (U_atom E 33 2 E33 ltac:(lia)), U_SLit. reflexivity.
Qed.

(* the registers the join keeps are never written by these runs *)
Definition w6c7_clob : list (bv 5) := [1; 10; 11; 12; 13; 20; 24; 25]%bv.
Lemma w6c7_rnz : forall r : bv 5, bv_eqb r 0 = false -> r <> 0%bv.
Proof. intros r H X. rewrite X in H. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate H. Qed.

Ltac w6c7_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).
Ltac w6c7_kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; w6c7_kio].
Ltac w6c7_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e
  end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6C_CPY.

(* ===================== the leaf: the call's state 0x510d4 -> the join ===================== *)
Lemma w6c7_fin : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa r
(regs2 : bvmap 5 word) mem2 md2 ty sz (bs : list byte) src cur' nl' ed,
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa r ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io mdc md2 ->
(forall rr, In rr w6c_keep -> getr regs2 rr = getr regs rr) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (F + 0xf0 <= a < F + 0xf8) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
getr regs2 1 = w64 W6C_RCPY -> getr regs2 10 = w64 (F + 0xf8) -> getr regs2 11 = w64 src ->
getr regs2 12 = w64 (Z.of_nat (length bs)) -> getr regs2 20 = w64 sa -> getr regs2 25 = w64 cur' ->
val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf0) 4 ty ->
val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf4) 4 sz ->
val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xf8) 8 (nl' mod 2 ^ 64) ->
rm_bytes rsegs (w_H W) memc src bs -> cur <= src -> src + Z.of_nat (length bs) <= cur + Z.of_nat (length r) ->
(length bs <= Z.to_nat sz)%nat -> 0 <= sz <= 96 ->
ed = Ent ty sz (bs ++ zeros (Z.to_nat sz - length bs)) ->
SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 W6C_CPY) mem2 (seg_rom rsegs)) md2)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F ed cur' nl' sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa r regs2 mem2 md2 ty sz bs src
cur' nl' ed Hctx Hin HJ2 Hio2 Hk2 KE H1 H10 H11 H12 H20 H25 Vty Vsz Vnl Hbs Hs1 Hs2 Hlen Hsz ->.
pose proof Hctx as (HJ & HG & Hrom).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFe & HFapp & HF32).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
destruct Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Vm & Vb0 & Hsa & Vc0 & Vf0 & Vf8 & Hz & Hfsh
  & Hr & Hra & Hhull & Hamr & Hcur1 & Hcur2 & Hdis & Ht6 & Ht8 & Htf).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
assert (HSH : forall x, SHADOW_OFF - 8 <= x < SHADOW_OFF + 2 ^ 44 + 64 ->
  aview rsegs (w_H W) mem2 x = aview rsegs (w_H W) memc x)
  by (apply (w6c7_shadow_eq W memc mem2 R F KE); [unfold T_SEG_STK, ASTACK in *; lia | exact HFapp]).
assert (Hlr : 0 <= Z.of_nat (length r)) by lia.
eapply SRr_mono;
[ apply (w6c_tail_cpy B AMEMCPY STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem2 md2 regs2 R F pos ty sz src bs
  cur' nl' sa HJ2 HG H1)
| cbv beta; intros W2 c2 _ HQ;
  exact (w6c_jpost_trans B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mem2 md2 regs2 R F _
    cur' nl' sa W2 c2 Hk2 Hio2 ltac:(intros a Ha X Y Z0; apply KE; [exact Ha | lia | lia]) HQ) ].
- rewrite (Hk2 (2%bv) ltac:(cbv [w6c_keep In]; tauto)). exact D2.
- rewrite (Hk2 (3%bv) ltac:(cbv [w6c_keep In]; tauto)). exact D3.
- rewrite (Hk2 (4%bv) ltac:(cbv [w6c_keep In]; tauto)). exact D4.
- exact H10.
- exact H11.
- exact H12.
- exact H20.
- exact H25.
- exact Hlen.
- exact Hsz.
- apply (w6c_e_hdr (w_H W) memc mem2 F ty sz).
  + exact Hz.
  + exact Vty.
  + exact Vsz.
  + intros x Hx. apply KE; unfold T_SEG_STK, ASTACK in *; lia.
- apply (rm_bytes_kept rsegs (w_H W) memc); [exact Hbs|]. intros x Hx.
  destruct (Hdis x ltac:(lia)) as [Hd1 Hd2]. apply KE; unfold T_SEG_STK, ASTACK in *; lia.
- apply (w6c7_ra_tr W memc mem2); [| exact HSH | lia | lia].
  apply (ra_sub _ _ cur (Z.of_nat (length r))); [exact Hra | lia | lia].
- intros Hn0. apply (w6c7_hull_tr W memc mem2); [| exact HSH | lia | lia | lia].
  apply (rm_hull_sub _ cur (Z.of_nat (length r))); [apply Hhull; lia | lia | lia | lia].
- unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr |- *. lia.
- lia.
- lia.
- intros a Ha. destruct (Hdis a ltac:(lia)) as [Hd1 Hd2]. unfold ESTACK, T_SEG_STK, ASTACK in *.
  split; lia.
- apply (w6c7_fsh_tr W memc mem2 F rs_PJ Hfsh HSH); [lia | lia | vm_compute; intros X; discriminate X].
- exact Vnl.
Qed.

(* ===================== r = [] : one run, s9 pinned to the literal 0 ===================== *)
Lemma w6c7_case0 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa,
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa [] ->
SRr rsegs W (cfg_at rsegs W6C_D7 regs memc mdc)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
 (fst (w6c_ent 7 [])) (cur + Z.of_nat (length ([] : list byte) - length (snd (w6c_ent 7 []))))
 (Z.of_nat (length (snd (w6c_ent 7 [])))) sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa Hctx Hin.
pose proof Hctx as (HJ & HG & Hrom).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFe & HFapp & HF32).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
destruct (w6c_present B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx) as (HpF & HpR).
pose proof Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Vm & Vb0 & Hsa & Vc0 & Vf0 & Vf8 & Hz & Hfsh
  & Hr & Hra & Hhull & Hamr & Hcur1 & Hcur2 & Hdis & Ht6 & Ht8 & Htf).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
assert (HN0 : Z.of_nat (length ([] : list byte)) = 0) by reflexivity.
assert (HZ0 : Z.of_nat 0%nat = 0) by reflexivity.
assert (HRlo : 0x10007fff8000 + 16384 <= R) by (unfold kHighMemBeg, T_SEG_STK, ASTACK in HRk; lia).
assert (HSTK' : sp0 - STK <= R - 16384) by (unfold T_SEG_STK, ASTACK in HSTK; lia).
assert (HFR : F + 512 <= R - 16384) by (unfold T_SEG_STK, ASTACK in HRc; lia).
set (NN := Z.of_nat (length ([] : list byte)) + 1) in *.
assert (HNN : NN = 1) by (unfold NN; lia).
assert (U9 : bv_unsigned (ew (Ereg regs (w6c_extra F NN 0 sa 0)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 (9%bv) eq_refl), D9; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (Ereg regs (w6c_extra F NN 0 sa 0)) 32) = F)
  by (rewrite w6c_e32; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (w6c_extra F NN 0 sa 0)) 32 = Z_to_bv 64 F) by apply w6c_e32.
assert (E33 : ew (Ereg regs (w6c_extra F NN 0 sa 0)) 33 = Z_to_bv 64 NN) by apply w6c_e33.
assert (E35 : ew (Ereg regs (w6c_extra F NN 0 sa 0)) 35 = Z_to_bv 64 sa) by apply w6c_e35.
assert (E14 : ew (Ereg regs (w6c_extra F NN 0 sa 0)) 14 = Z_to_bv 64 (cur - 1))
  by (rewrite (ew_Ereg_nat regs _ 14 (14%bv) eq_refl); exact D14).
assert (E23 : ew (Ereg regs (w6c_extra F NN 0 sa 0)) 23 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 23 (23%bv) eq_refl); exact D23).
assert (U23 : bv_unsigned (ew (Ereg regs (w6c_extra F NN 0 sa 0)) 23) = 0x7fff8000)
  by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U14 : bv_unsigned (ew (Ereg regs (w6c_extra F NN 0 sa 0)) 14) = cur - 1)
  by (rewrite E14; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (Ereg regs (w6c_extra F NN 0 sa 0)) 33) = NN)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (Ereg regs (w6c_extra F NN 0 sa 0)) 34) = 0)
  by (rewrite w6c_e34; reflexivity).
assert (U36 : bv_unsigned (ew (Ereg regs (w6c_extra F NN 0 sa 0)) 36) = 0)
  by (rewrite w6c_e36; reflexivity).
assert (V0 : val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf0) 4 0).
{ replace (F + 0xf0) with (F + 0xf0 + Z.of_nat 0) by lia.
  apply (rm_bytes_field rsegs (w_H W) memc (F + 0xf0) (zeros 104) 0 4 0 Hz);
    [reflexivity | rewrite length_zeros; lia]. }
assert (V4 : val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf4) 4 0).
{ replace (F + 0xf4) with (F + 0xf0 + Z.of_nat 4) by lia.
  apply (rm_bytes_field rsegs (w_H W) memc (F + 0xf0) (zeros 104) 4 4 0 Hz);
    [reflexivity | rewrite length_zeros; lia]. }
assert (HS : st_ok rsegs (Ereg regs (w6c_extra F NN 0 sa 0))
  (mkSS W6C_D7 w6c_sr [w6c_RS; w6c_RE] None (mkFacts (w6c_facts 1 1 (2 ^ 47 - 2)) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - change w6c_sr with (sr_set (sr_set sr_atoms (24%bv : bv 5) (SOff 14 1)) (25%bv : bv 5) (SOff 33 (-1))).
    apply (regs_ok_pin _ _ _ (25%bv : bv 5) (SOff 33 (-1))).
    + apply (regs_ok_pin _ _ _ (24%bv : bv 5) (SOff 14 1)).
      * apply regs_ok_Ereg.
      * apply w6c7_rnz. reflexivity.
      * rewrite D24, (w6c7_soff _ 14 (cur - 1) 1 E14 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
    + apply w6c7_rnz. reflexivity.
    + rewrite D25, (w6c7_soff _ 33 NN (-1) E33 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (w6c_RS_ok (Ereg regs (w6c_extra F NN 0 sa 0)) W memc R F NN sa U9
        ltac:(apply w6c_e32) ltac:(apply w6c_e33) ltac:(apply w6c_e35)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsa
        ltac:(intros o Ho; apply HpR; lia) Vm Vb0 Vc0 Vf0 Vf8).
    + apply (w6c_RE_ok (Ereg regs (w6c_extra F NN 0 sa 0)) W memc F U32 ltac:(lia) ltac:(lia)
        ltac:(intros o Ho; apply HpF; lia) V0 V4).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, w6c_RS, w6c_RE.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    split; [split; [right; lia | exact I] | split; exact I].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
    apply (w6c_facts_ok _ R F (cur - 1) NN 0 0 1 1 (2 ^ 47 - 2) U9 U32 U23 U14 U33 U34 U36);
      [lia | exact HR16 | lia | exact HF32 | lia | lia | lia | lia]. }
pose proof (st_ok_pin_lit rsegs _ _ _ (25%bv : bv 5) 0 HS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite D25; unfold w64; rewrite HN0; reflexivity)) as HS1.
clear HS. rename HS1 into HS.
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F NN 0 sa 0)) (mrestrict (w_H W) memc)).
{ apply (w6c_shok _ W memc F).
  - unfold w6c_Bx. apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 32 F E32). lia.
  - replace (F + 0xf0) with (F + RM_E + 0) by (unfold RM_E; lia).
    apply (rm_A_ra_e rsegs (w_H W) memc F false false false false 0 8);
      [rewrite <- rs_PJ_sh; exact Hfsh | apply w6c_F8; exact HF32 | lia | lia].
  - exact HFapp. }
assert (HAE : env_agree 32 (Ereg regs (w6c_extra F NN 0 sa 0)) (Ereg regs (w6c_extra F NN 0 sa 0)))
  by apply env_agree_refl.
pose proof (AR_laws_ok rsegs B) as HL. pose proof w6c_segs_low as Hsl. pose proof w6c_wx as Hwx.
unfold cfg_at. change (w64 W6C_D7) with (Z_to_bv 64 W6C_D7).
aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_CPY.
{ apply (w6c7_awr_ok _ _ R F); [exact U9 | exact U32 | vm_compute; reflexivity | lia | lia | exact HFw]. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (F + 0xf0 <= a < F + 0xf8) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ lazymatch goal with HFx : frame_of ?E0 ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply (w6c7_keep1 E0 rs R F memc memc (ms_mem ms) W ltac:(intros a Ha X Y; reflexivity) HFx
      ltac:(vm_compute; reflexivity) U9 U32) end. }
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msx HSx eq_refl) at 1 end.
rewrite w6c7_ent0. cbn [fst snd length Nat.sub].
eapply (w6c7_fin STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa [] _ _ _
  0 0 [] cur (cur + Z.of_nat 0) (Z.of_nat 0) (Ent 0 0 []) Hctx Hin).
- assumption.
- w6c7_kio.
- intros rr Hrr. apply (regs_kept_of_st_ok rsegs _ _ ms regs (w6c_extra F NN 0 sa 0) (w_H W) w6c7_clob HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) rr).
  + cbv [w6c_keep In] in Hrr. repeat (destruct Hrr as [<-|Hrr]; [vm_compute; discriminate|]). destruct Hrr.
  + cbv [w6c_keep In] in Hrr.
    repeat (destruct Hrr as [<-|Hrr]; [cbv [w6c7_clob In]; intros X;
      repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hrr.
- exact KE.
- w6c7_reg HS (1%bv : bv 5). reflexivity.
- w6c7_reg HS (10%bv : bv 5).
  rewrite (w6c7_soff _ 32 F 248 E32 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
- w6c7_reg HS (11%bv : bv 5).
  rewrite (w6c7_soff _ 14 (cur - 1) 1 E14 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
- w6c7_reg HS (12%bv : bv 5). unfold w64. rewrite HN0. reflexivity.
- w6c7_reg HS (20%bv : bv 5).
  rewrite (w6c7_soff _ 35 sa 0 E35 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
- w6c7_reg HS (25%bv : bv 5).
  rewrite (w6c7_soff _ 14 (cur - 1) 1 E14 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
- apply (w6c7_chunk _ _ ms (w_H W) 1%nat _ 240 4%N (SLit 0) 0 32%nat F HS
    ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) U32 ltac:(reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)).
- apply (w6c7_chunk _ _ ms (w_H W) 1%nat _ 244 4%N (SLit 0) 0 32%nat F HS
    ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) U32 ltac:(reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)).
- change (Z.of_nat 0 mod 2 ^ 64) with 0.
  apply (w6c7_chunk _ _ ms (w_H W) 0%nat _ 248 8%N (SLit 0) 0 9%nat R HS
    ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) U9 ltac:(reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)).
- apply (proj2 (rm_bytes_aview rsegs (w_H W) memc cur [])). intros i Hi. cbn [length] in Hi. lia.
- lia.
- lia.
- cbn [length]. lia.
- lia.
- reflexivity.
Qed.

(* ===================== r = [t] : the `bne a1,2` arm that keeps [R+0xf8] = 2 is impossible ===================== *)
Lemma w6c7_case1 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa (t0 : byte),
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa [t0] ->
SRr rsegs W (cfg_at rsegs W6C_D7 regs memc mdc)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
 (fst (w6c_ent 7 [t0])) (cur + Z.of_nat (length [t0] - length (snd (w6c_ent 7 [t0]))))
 (Z.of_nat (length (snd (w6c_ent 7 [t0])))) sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa t0 Hctx Hin.
pose proof Hctx as (HJ & HG & Hrom).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFe & HFapp & HF32).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
destruct (w6c_present B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx) as (HpF & HpR).
pose proof Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Vm & Vb0 & Hsa & Vc0 & Vf0 & Vf8 & Hz & Hfsh
  & Hr & Hra & Hhull & Hamr & Hcur1 & Hcur2 & Hdis & Ht6 & Ht8 & Htf).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
pose proof (Cursor.byte_range t0) as Hbt.
assert (HN1 : Z.of_nat (length [t0]) = 1) by reflexivity.
assert (HZ0 : Z.of_nat 0%nat = 0) by reflexivity.
assert (HZ1 : Z.of_nat 1%nat = 1) by reflexivity.
assert (HRlo : 0x10007fff8000 + 16384 <= R) by (unfold kHighMemBeg, T_SEG_STK, ASTACK in HRk; lia).
assert (HSTK' : sp0 - STK <= R - 16384) by (unfold T_SEG_STK, ASTACK in HSTK; lia).
assert (HFR : F + 512 <= R - 16384) by (unfold T_SEG_STK, ASTACK in HRc; lia).
destruct (Hdis cur ltac:(lia)) as (Hdc1 & Hdc2).
unfold T_SEG_STK, ASTACK in Hdc1.
assert (Vf8' : val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 2)
  by (replace 2 with (Z.of_nat (length [t0]) + 1) by lia; exact Vf8).
assert (Vt : val_mem rsegs (mrestrict (w_H W) memc) (cur - 1 + 1) 1 (bv_unsigned t0)).
{ replace (cur - 1 + 1) with (cur + Z.of_nat 0) by lia.
  exact (rm_bytes_byte rsegs (w_H W) memc cur [t0] 0 Hr ltac:(cbn [length]; lia)). }
assert (U9 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 (9%bv) eq_refl), D9; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 32) = F)
  by (rewrite w6c_e32; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 32 = Z_to_bv 64 F) by apply w6c_e32.
assert (E33 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 33 = Z_to_bv 64 2) by apply w6c_e33.
assert (E34 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 34 = Z_to_bv 64 (bv_unsigned t0))
  by apply w6c_e34.
assert (E35 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 35 = Z_to_bv 64 sa) by apply w6c_e35.
assert (E36 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 36 = Z_to_bv 64 0) by apply w6c_e36.
assert (E14 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 14 = Z_to_bv 64 (cur - 1))
  by (rewrite (ew_Ereg_nat regs _ 14 (14%bv) eq_refl); exact D14).
assert (E23 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 23 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 23 (23%bv) eq_refl); exact D23).
assert (U23 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 23) = 0x7fff8000)
  by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U14 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 14) = cur - 1)
  by (rewrite E14; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 33) = 2)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 34) = bv_unsigned t0)
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) 36) = 0)
  by (rewrite E36; apply unsigned_lit_small; lia).
assert (V0 : val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf0) 4 0).
{ replace (F + 0xf0) with (F + 0xf0 + Z.of_nat 0) by lia.
  apply (rm_bytes_field rsegs (w_H W) memc (F + 0xf0) (zeros 104) 0 4 0 Hz);
    [reflexivity | rewrite length_zeros; lia]. }
assert (V4 : val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf4) 4 0).
{ replace (F + 0xf4) with (F + 0xf0 + Z.of_nat 4) by lia.
  apply (rm_bytes_field rsegs (w_H W) memc (F + 0xf0) (zeros 104) 4 4 0 Hz);
    [reflexivity | rewrite length_zeros; lia]. }
assert (HS : st_ok rsegs (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0))
  (mkSS W6C_D7 w6c_sr [w6c_RS; w6c_RE; w6c_RI 1] None (mkFacts (w6c_facts 2 2 (2 ^ 47 - 3)) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - change w6c_sr with (sr_set (sr_set sr_atoms (24%bv : bv 5) (SOff 14 1)) (25%bv : bv 5) (SOff 33 (-1))).
    apply (regs_ok_pin _ _ _ (25%bv : bv 5) (SOff 33 (-1))).
    + apply (regs_ok_pin _ _ _ (24%bv : bv 5) (SOff 14 1)).
      * apply regs_ok_Ereg.
      * apply w6c7_rnz. reflexivity.
      * rewrite D24, (w6c7_soff _ 14 (cur - 1) 1 E14 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
    + apply w6c7_rnz. reflexivity.
    + rewrite D25, (w6c7_soff _ 33 2 (-1) E33 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (w6c_RS_ok (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) W memc R F 2 sa U9
        ltac:(apply w6c_e32) ltac:(apply w6c_e33) ltac:(apply w6c_e35)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsa
        ltac:(intros o Ho; apply HpR; lia) Vm Vb0 Vc0 Vf0 Vf8').
    + apply (w6c_RE_ok (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) W memc F U32 ltac:(lia) ltac:(lia)
        ltac:(intros o Ho; apply HpF; lia) V0 V4).
    + apply (w6c_RI_ok (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0)) W memc (cur - 1) (bv_unsigned t0) 0 1
        U14 E34 E36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(intros _; exact Vt) ltac:(intros X; exfalso; lia)).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, w6c_RS, w6c_RE, w6c_RI.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U14.
    split; [split; [right; lia | split; [lia | exact I]] | split; [split; [lia | exact I] | split; exact I]].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
    apply (w6c_facts_ok _ R F (cur - 1) 2 (bv_unsigned t0) 0 2 2 (2 ^ 47 - 3) U9 U32 U23 U14 U33 U34 U36);
      [lia | exact HR16 | lia | exact HF32 | lia | lia | lia | lia]. }
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0))
  (mrestrict (w_H W) memc)).
{ apply (w6c_shok _ W memc F).
  - unfold w6c_Bx. apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 32 F E32). lia.
  - replace (F + 0xf0) with (F + RM_E + 0) by (unfold RM_E; lia).
    apply (rm_A_ra_e rsegs (w_H W) memc F false false false false 0 8);
      [rewrite <- rs_PJ_sh; exact Hfsh | apply w6c_F8; exact HF32 | lia | lia].
  - exact HFapp. }
assert (HAE : env_agree 32 (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0))
  (Ereg regs (w6c_extra F 2 (bv_unsigned t0) sa 0))) by apply env_agree_refl.
pose proof (AR_laws_ok rsegs B) as HL. pose proof w6c_segs_low as Hsl. pose proof w6c_wx as Hwx.
unfold cfg_at. change (w64 W6C_D7) with (Z_to_bv 64 W6C_D7).
aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_CPY.
{ apply (obl_of_range rsegs (w_H W) memc _ w6c_Bx _ _ cur (Z.of_nat (length [t0]))).
  - exact Hra.
  - unfold w6c_Bx. apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
  - rewrite (w6c_U_cur _ (cur - 1) 1 U14 ltac:(lia)). lia.
  - rewrite (w6c_U_cur _ (cur - 1) 1 U14 ltac:(lia)). lia. }
{ apply (w6c7_awr_ok _ _ R F); [exact U9 | exact U32 | vm_compute; reflexivity | lia | lia | exact HFw]. }
lazymatch type of HS with st_ok _ ?E1 _ _ =>
  assert (E33' : ew E1 33 = Z_to_bv 64 2) by (rewrite ?ew_ewset_other by lia; exact E33) end.
srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan.
- exfalso. exact (w6c7_ne2 _ E33' Hc).
- aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_CPY.
  { apply (w6c7_awr_ok _ _ R F);
    [ rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32
    | vm_compute; reflexivity | lia | lia | exact HFw]. }
  lazymatch goal with
  | HF1 : frame_of ?E0 ?rs0 (mrestrict _ memc) (mrestrict _ ?m1),
    HF2 : frame_of ?E1 ?rs1 (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (F + 0xf0 <= a < F + 0xf8) ->
      aview rsegs (w_H W) m2 a = aview rsegs (w_H W) memc a)
    by (apply (w6c7_keep1 E1 rs1 R F memc m1 m2 W
          (w6c7_keep1 E0 rs0 R F memc memc m1 W ltac:(intros a Ha X Y; reflexivity) HF1
             ltac:(vm_compute; reflexivity) U9 U32)
          HF2 ltac:(vm_compute; reflexivity)
          ltac:(rewrite ?ew_ewset_other by lia; exact U9)
          ltac:(rewrite ?ew_ewset_other by lia; exact U32)))
  end.
  lazymatch type of HS with st_ok _ ?E2 _ _ =>
    assert (F32 : ew E2 32 = Z_to_bv 64 F) by (rewrite ?ew_ewset_other by lia; exact E32);
    assert (F14 : ew E2 14 = Z_to_bv 64 (cur - 1)) by (rewrite ?ew_ewset_other by lia; exact E14);
    assert (F35 : ew E2 35 = Z_to_bv 64 sa) by (rewrite ?ew_ewset_other by lia; exact E35);
    assert (F34 : ew E2 34 = Z_to_bv 64 (bv_unsigned t0)) by (rewrite ?ew_ewset_other by lia; exact E34);
    assert (G9 : bv_unsigned (ew E2 9) = R) by (rewrite ?ew_ewset_other by lia; exact U9);
    assert (G32 : bv_unsigned (ew E2 32) = F) by (rewrite ?ew_ewset_other by lia; exact U32)
  end.
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msx HSx eq_refl) at 1 end.
  rewrite w6c7_ent1. cbn [fst snd length Nat.sub].
  eapply (w6c7_fin STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa [t0] _ _ _
    (bv_unsigned t0 mod 21) 0 [] (cur + 1) (cur + Z.of_nat 1) (Z.of_nat 0)
    (Ent (bv_unsigned t0 mod 21) 0 []) Hctx Hin).
  + assumption.
  + w6c7_kio.
  + intros rr Hrr.
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (regs_kept_of_st_ok rsegs _ _ msx regs (w6c_extra F 2 (bv_unsigned t0) sa 0) (w_H W) w6c7_clob HSx
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) rr) end.
    * cbv [w6c_keep In] in Hrr. repeat (destruct Hrr as [<-|Hrr]; [vm_compute; discriminate|]). destruct Hrr.
    * cbv [w6c_keep In] in Hrr.
      repeat (destruct Hrr as [<-|Hrr]; [cbv [w6c7_clob In]; intros X;
        repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hrr.
  + exact KE.
  + w6c7_reg HS (1%bv : bv 5). reflexivity.
  + w6c7_reg HS (10%bv : bv 5).
    rewrite (w6c7_soff _ 32 F 248 F32 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + w6c7_reg HS (11%bv : bv 5).
    rewrite (w6c7_soff _ 14 (cur - 1) 2 F14 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + w6c7_reg HS (12%bv : bv 5). unfold w64. cbn [length]. rewrite HZ0. reflexivity.
  + w6c7_reg HS (20%bv : bv 5).
    rewrite (w6c7_soff _ 35 sa 0 F35 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + w6c7_reg HS (25%bv : bv 5).
    rewrite (w6c7_soff _ 14 (cur - 1) 2 F14 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (w6c7_chunk _ _ msx (w_H W) 1%nat _ 240 4%N w6c_e7t (bv_unsigned t0 mod 21) 32%nat F HSx
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) G32
        ltac:(apply (w6c_t21 _ (bv_unsigned t0) F34); lia)
        ltac:(cbn; pose proof (Z.mod_pos_bound (bv_unsigned t0) 21 ltac:(lia)); lia) ltac:(cbn; lia)) end.
  + lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (w6c7_chunk _ _ msx (w_H W) 1%nat _ 244 4%N (SLit 0) 0 32%nat F HSx
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) G32 ltac:(reflexivity)
        ltac:(cbn; lia) ltac:(cbn; lia)) end.
  + change (Z.of_nat 0 mod 2 ^ 64) with 0.
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (w6c7_chunk _ _ msx (w_H W) 0%nat _ 248 8%N (SLit 0) 0 9%nat R HSx
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) G9 ltac:(reflexivity)
        ltac:(cbn; lia) ltac:(cbn; lia)) end.
  + apply (proj2 (rm_bytes_aview rsegs (w_H W) memc (cur + 1) [])). intros i Hi. cbn [length] in Hi. lia.
  + lia.
  + cbn [length]. lia.
  + cbn [length]. lia.
  + lia.
  + reflexivity.
Qed.

(* ===================== r = t :: s :: r' : the engine stops at `bltu a2,a1` 0x814d0 ===================== *)
Lemma w6c7_case2 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa
(t0 s0 : byte) (rest : list byte),
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa (t0 :: s0 :: rest) ->
SRr rsegs W (cfg_at rsegs W6C_D7 regs memc mdc)
(w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
 (fst (w6c_ent 7 (t0 :: s0 :: rest)))
 (cur + Z.of_nat (length (t0 :: s0 :: rest) - length (snd (w6c_ent 7 (t0 :: s0 :: rest)))))
 (Z.of_nat (length (snd (w6c_ent 7 (t0 :: s0 :: rest))))) sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa t0 s0 rest Hctx Hin.
pose proof Hctx as (HJ & HG & Hrom).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFe & HFapp & HF32).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
destruct (w6c_present B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx) as (HpF & HpR).
pose proof Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Vm & Vb0 & Hsa & Vc0 & Vf0 & Vf8 & Hz & Hfsh
  & Hr & Hra & Hhull & Hamr & Hcur1 & Hcur2 & Hdis & Ht6 & Ht8 & Htf).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
pose proof (Cursor.byte_range t0) as Hbt. pose proof (Cursor.byte_range s0) as Hbs0.
pose proof (Z.mod_pos_bound (bv_unsigned s0) 12 ltac:(lia)) as Hsmod.
pose proof (Z.mod_pos_bound (bv_unsigned t0) 21 ltac:(lia)) as Htmod.
assert (HLc : length (t0 :: s0 :: rest) = (length rest + 2)%nat) by (cbn [length]; lia).
assert (HLs : length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest)
  = (length rest - Z.to_nat (bv_unsigned s0 mod 12))%nat)
  by apply length_skipn.
assert (HLf : length (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest)
  = Nat.min (Z.to_nat (bv_unsigned s0 mod 12)) (length rest))
  by apply length_firstn.
rewrite HLc in Hcur2, Hdis, Hra, Hhull, Hamr.
assert (HRlo : 0x10007fff8000 + 16384 <= R) by (unfold kHighMemBeg, T_SEG_STK, ASTACK in HRk; lia).
assert (HSTK' : sp0 - STK <= R - 16384) by (unfold T_SEG_STK, ASTACK in HSTK; lia).
assert (HFR : F + 512 <= R - 16384) by (unfold T_SEG_STK, ASTACK in HRc; lia).
destruct (Hdis cur ltac:(lia)) as (Hdc1 & Hdc2).
unfold T_SEG_STK, ASTACK in Hdc1.
assert (Vf8' : val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (Z.of_nat (length rest) + 3)).
{ replace (Z.of_nat (length rest) + 3) with (Z.of_nat (length (t0 :: s0 :: rest)) + 1)
    by (rewrite HLc; lia). exact Vf8. }
assert (Vt : val_mem rsegs (mrestrict (w_H W) memc) (cur - 1 + 1) 1 (bv_unsigned t0)).
{ replace (cur - 1 + 1) with (cur + Z.of_nat 0) by lia.
  exact (rm_bytes_byte rsegs (w_H W) memc cur (t0 :: s0 :: rest) 0 Hr ltac:(rewrite HLc; lia)). }
assert (Vs : val_mem rsegs (mrestrict (w_H W) memc) (cur - 1 + 2) 1 (bv_unsigned s0)).
{ replace (cur - 1 + 2) with (cur + Z.of_nat 1) by lia.
  exact (rm_bytes_byte rsegs (w_H W) memc cur (t0 :: s0 :: rest) 1 Hr ltac:(rewrite HLc; lia)). }
assert (Hrest : rm_bytes rsegs (w_H W) memc (cur + 2) rest).
{ destruct (proj1 (rm_bytes_app rsegs (w_H W) memc cur [t0; s0] rest) Hr) as (_ & Hx).
  replace (cur + 2) with (cur + Z.of_nat (length [t0; s0])) by (cbn [length]; lia). exact Hx. }
assert (Hbs : rm_bytes rsegs (w_H W) memc (cur + 2) (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest)).
{ destruct (proj1 (rm_bytes_app rsegs (w_H W) memc (cur + 2)
    (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest) (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest))
    ltac:(rewrite firstn_skipn; exact Hrest)) as (Hx & _). exact Hx. }
assert (U9 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0))) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 (9%bv) eq_refl), D9; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0))) 32) = F)
  by (rewrite w6c_e32; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa (bv_unsigned s0))) 32
  = Z_to_bv 64 F) by apply w6c_e32.
assert (E33 : ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa (bv_unsigned s0))) 33
  = Z_to_bv 64 (Z.of_nat (length rest) + 3)) by apply w6c_e33.
assert (E34 : ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa (bv_unsigned s0))) 34
  = Z_to_bv 64 (bv_unsigned t0)) by apply w6c_e34.
assert (E35 : ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa (bv_unsigned s0))) 35
  = Z_to_bv 64 sa) by apply w6c_e35.
assert (E36 : ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa (bv_unsigned s0))) 36
  = Z_to_bv 64 (bv_unsigned s0)) by apply w6c_e36.
assert (E14 : ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa (bv_unsigned s0))) 14
  = Z_to_bv 64 (cur - 1)) by (rewrite (ew_Ereg_nat regs _ 14 (14%bv) eq_refl); exact D14).
assert (E23 : ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa (bv_unsigned s0))) 23
  = Z_to_bv 64 SHADOW_OFF) by (rewrite (ew_Ereg_nat regs _ 23 (23%bv) eq_refl); exact D23).
assert (U23 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0))) 23) = 0x7fff8000)
  by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U14 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0))) 14) = cur - 1) by (rewrite E14; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0))) 33) = Z.of_nat (length rest) + 3) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0))) 34) = bv_unsigned t0) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0))) 36) = bv_unsigned s0) by (rewrite E36; apply unsigned_lit_small; lia).
assert (V0 : val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf0) 4 0).
{ replace (F + 0xf0) with (F + 0xf0 + Z.of_nat 0) by lia.
  apply (rm_bytes_field rsegs (w_H W) memc (F + 0xf0) (zeros 104) 0 4 0 Hz);
    [reflexivity | rewrite length_zeros; lia]. }
assert (V4 : val_mem rsegs (mrestrict (w_H W) memc) (F + 0xf4) 4 0).
{ replace (F + 0xf4) with (F + 0xf0 + Z.of_nat 4) by lia.
  apply (rm_bytes_field rsegs (w_H W) memc (F + 0xf0) (zeros 104) 4 4 0 Hz);
    [reflexivity | rewrite length_zeros; lia]. }
assert (HS : st_ok rsegs (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0)))
  (mkSS W6C_D7 w6c_sr [w6c_RS; w6c_RE; w6c_RI 2] None (mkFacts (w6c_facts 3 (2 ^ 47) (2 ^ 47 - 4)) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - change w6c_sr with (sr_set (sr_set sr_atoms (24%bv : bv 5) (SOff 14 1)) (25%bv : bv 5) (SOff 33 (-1))).
    apply (regs_ok_pin _ _ _ (25%bv : bv 5) (SOff 33 (-1))).
    + apply (regs_ok_pin _ _ _ (24%bv : bv 5) (SOff 14 1)).
      * apply regs_ok_Ereg.
      * apply w6c7_rnz. reflexivity.
      * rewrite D24, (w6c7_soff _ 14 (cur - 1) 1 E14 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
    + apply w6c7_rnz. reflexivity.
    + rewrite D25, (w6c7_soff _ 33 (Z.of_nat (length rest) + 3) (-1) E33 ltac:(lia) ltac:(lia)).
      unfold w64; f_equal; rewrite HLc; lia.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (w6c_RS_ok _ W memc R F (Z.of_nat (length rest) + 3) sa U9
        ltac:(apply w6c_e32) ltac:(apply w6c_e33) ltac:(apply w6c_e35)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsa
        ltac:(intros o Ho; apply HpR; lia) Vm Vb0 Vc0 Vf0 Vf8').
    + apply (w6c_RE_ok _ W memc F U32 ltac:(lia) ltac:(lia) ltac:(intros o Ho; apply HpF; lia) V0 V4).
    + apply (w6c_RI_ok _ W memc (cur - 1) (bv_unsigned t0) (bv_unsigned s0) 2
        U14 E34 E36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(intros _; exact Vt) ltac:(intros _; exact Vs)).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, w6c_RS, w6c_RE, w6c_RI.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U14.
    split; [split; [right; lia | split; [lia | exact I]] | split; [split; [lia | exact I] | split; exact I]].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
    apply (w6c_facts_ok _ R F (cur - 1) (Z.of_nat (length rest) + 3) (bv_unsigned t0) (bv_unsigned s0)
      3 (2 ^ 47) (2 ^ 47 - 4) U9 U32 U23 U14 U33 U34 U36);
      [lia | exact HR16 | lia | exact HF32 | lia | lia | lia | lia]. }
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0)
  sa (bv_unsigned s0))) (mrestrict (w_H W) memc)).
{ apply (w6c_shok _ W memc F).
  - unfold w6c_Bx. apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 32 F E32). lia.
  - replace (F + 0xf0) with (F + RM_E + 0) by (unfold RM_E; lia).
    apply (rm_A_ra_e rsegs (w_H W) memc F false false false false 0 8);
      [rewrite <- rs_PJ_sh; exact Hfsh | apply w6c_F8; exact HF32 | lia | lia].
  - exact HFapp. }
assert (HAE : env_agree 32 (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0))) (Ereg regs (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa
  (bv_unsigned s0)))) by apply env_agree_refl.
pose proof (AR_laws_ok rsegs B) as HL. pose proof w6c_segs_low as Hsl. pose proof w6c_wx as Hwx.
unfold cfg_at. change (w64 W6C_D7) with (Z_to_bv 64 W6C_D7).
aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_CPY.
{ apply (obl_of_range rsegs (w_H W) memc _ w6c_Bx _ _ cur (Z.of_nat (length rest + 2))).
  - exact Hra.
  - unfold w6c_Bx. apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
  - rewrite (w6c_U_cur _ (cur - 1) 2 U14 ltac:(lia)). lia.
  - rewrite (w6c_U_cur _ (cur - 1) 2 U14 ltac:(lia)). lia. }
{ apply (obl_of_range rsegs (w_H W) memc _ w6c_Bx _ _ cur (Z.of_nat (length rest + 2))).
  - exact Hra.
  - unfold w6c_Bx. apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
  - rewrite (w6c_U_cur _ (cur - 1) 1 U14 ltac:(lia)). lia.
  - rewrite (w6c_U_cur _ (cur - 1) 1 U14 ltac:(lia)). lia. }
{ apply (w6c7_awr_ok _ _ R F); [exact U9 | exact U32 | vm_compute; reflexivity | lia | lia | exact HFw]. }
lazymatch type of HS with st_ok _ ?E1 _ _ =>
  assert (B33 : ew E1 33 = Z_to_bv 64 (Z.of_nat (length rest) + 3))
    by (rewrite ?ew_ewset_other by lia; exact E33);
  assert (B36 : ew E1 36 = Z_to_bv 64 (bv_unsigned s0))
    by (rewrite ?ew_ewset_other by lia; exact E36) end.
srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan.
- (* s % 12 < |r'| : the copy takes s % 12 bytes *)
  pose proof (w6c7_ltu_t _ (bv_unsigned s0) (Z.of_nat (length rest)) B36 Hbs0 B33 ltac:(lia) ltac:(lia) Hc)
    as HLT.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_CPY.
  { apply (w6c7_awr_ok _ _ R F);
    [ rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32
    | vm_compute; reflexivity | lia | lia | exact HFw]. }
  lazymatch type of HS with st_ok _ ?E2 _ _ =>
    assert (F32 : ew E2 32 = Z_to_bv 64 F) by (rewrite ?ew_ewset_other by lia; exact E32);
    assert (F14 : ew E2 14 = Z_to_bv 64 (cur - 1)) by (rewrite ?ew_ewset_other by lia; exact E14);
    assert (F35 : ew E2 35 = Z_to_bv 64 sa) by (rewrite ?ew_ewset_other by lia; exact E35);
    assert (F34 : ew E2 34 = Z_to_bv 64 (bv_unsigned t0)) by (rewrite ?ew_ewset_other by lia; exact E34);
    assert (F36 : ew E2 36 = Z_to_bv 64 (bv_unsigned s0)) by (rewrite ?ew_ewset_other by lia; exact E36);
    assert (F33 : ew E2 33 = Z_to_bv 64 (Z.of_nat (length rest) + 3))
      by (rewrite ?ew_ewset_other by lia; exact E33);
    assert (G9 : bv_unsigned (ew E2 9) = R) by (rewrite ?ew_ewset_other by lia; exact U9);
    assert (G32 : bv_unsigned (ew E2 32) = F) by (rewrite ?ew_ewset_other by lia; exact U32)
  end.
  lazymatch goal with
  | HF1 : frame_of ?E0 ?rs0 (mrestrict _ memc) (mrestrict _ ?m1),
    HF2 : frame_of ?E1 ?rs1 (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (F + 0xf0 <= a < F + 0xf8) ->
      aview rsegs (w_H W) m2 a = aview rsegs (w_H W) memc a)
    by (apply (w6c7_keep1 E1 rs1 R F memc m1 m2 W
          (w6c7_keep1 E0 rs0 R F memc memc m1 W ltac:(intros a Ha X Y; reflexivity) HF1
             ltac:(vm_compute; reflexivity) U9 U32)
          HF2 ltac:(vm_compute; reflexivity) G9 G32))
  end.
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msx HSx eq_refl) at 1 end.
  rewrite w6c7_ent2. cbn [fst snd].
  eapply (w6c7_fin STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa (t0 :: s0 :: rest)
    _ _ _ (bv_unsigned t0 mod 21) (bv_unsigned s0 mod 12)
    (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest) (cur + 2)
    (cur + Z.of_nat (length (t0 :: s0 :: rest) - length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest)))
    (Z.of_nat (length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest)))
    (Ent (bv_unsigned t0 mod 21) (bv_unsigned s0 mod 12)
      (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest
       ++ zeros (Z.to_nat (bv_unsigned s0 mod 12)
                 - length (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest)))) Hctx Hin).
  + assumption.
  + w6c7_kio.
  + intros rr Hrr.
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (regs_kept_of_st_ok rsegs _ _ msx regs
        (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa (bv_unsigned s0)) (w_H W) w6c7_clob HSx
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) rr) end.
    * cbv [w6c_keep In] in Hrr. repeat (destruct Hrr as [<-|Hrr]; [vm_compute; discriminate|]). destruct Hrr.
    * cbv [w6c_keep In] in Hrr.
      repeat (destruct Hrr as [<-|Hrr]; [cbv [w6c7_clob In]; intros X;
        repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hrr.
  + exact KE.
  + w6c7_reg HS (1%bv : bv 5). reflexivity.
  + w6c7_reg HS (10%bv : bv 5).
    rewrite (w6c7_soff _ 32 F 248 F32 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + w6c7_reg HS (11%bv : bv 5).
    rewrite (w6c7_soff _ 14 (cur - 1) 3 F14 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + w6c7_reg HS (12%bv : bv 5).
    etransitivity; [exact (w6c_s12 _ (bv_unsigned s0) F36 Hbs0)|].
    unfold w64; f_equal. rewrite HLf. lia.
  + w6c7_reg HS (20%bv : bv 5).
    rewrite (w6c7_soff _ 35 sa 0 F35 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + w6c7_reg HS (25%bv : bv 5).
    etransitivity;
    [ exact (w6c7_add _ (SOff 14 3) w6c_e7s (cur - 1 + 3) (bv_unsigned s0 mod 12)
        (w6c7_soff _ 14 (cur - 1) 3 F14 ltac:(lia) ltac:(lia))
        (w6c_s12 _ (bv_unsigned s0) F36 Hbs0) ltac:(lia) ltac:(lia) ltac:(lia)) |].
    unfold w64; f_equal. rewrite HLc, HLs. lia.
  + lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (w6c7_chunk _ _ msx (w_H W) 1%nat _ 240 4%N w6c_e7t (bv_unsigned t0 mod 21) 32%nat F HSx
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) G32
        ltac:(apply (w6c_t21 _ (bv_unsigned t0) F34); lia)
        ltac:(apply w6c7_w4; lia) ltac:(cbn; lia)) end.
  + lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (w6c7_chunk _ _ msx (w_H W) 1%nat _ 244 4%N w6c_e7s (bv_unsigned s0 mod 12) 32%nat F HSx
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) G32
        ltac:(exact (w6c_s12 _ (bv_unsigned s0) F36 Hbs0))
        ltac:(apply w6c7_w4; lia) ltac:(cbn; lia)) end.
  + assert (Hsm : Z.of_nat (length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest)) mod 2 ^ 64
      = Z.of_nat (length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest)))
      by (apply Z.mod_small; rewrite HLs; lia).
    rewrite Hsm.
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (w6c7_chunk _ _ msx (w_H W) 0%nat _ 248 8%N (SAlu ALU_SUB (SOff 33 (-3)) w6c_e7s)
        (Z.of_nat (length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest))) 9%nat R HSx
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) G9
        ltac:(replace (Z.of_nat (length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest)))
                with (Z.of_nat (length rest) + 3 + -3 - bv_unsigned s0 mod 12) by (rewrite HLs; lia);
              exact (w6c7_sub _ (SOff 33 (-3)) w6c_e7s (Z.of_nat (length rest) + 3 + -3)
                (bv_unsigned s0 mod 12)
                (w6c7_soff _ 33 (Z.of_nat (length rest) + 3) (-3) F33 ltac:(lia) ltac:(lia))
                (w6c_s12 _ (bv_unsigned s0) F36 Hbs0) ltac:(lia) ltac:(lia) ltac:(lia)))
        ltac:(apply w6c7_w8; rewrite HLs; lia) ltac:(cbn; lia)) end.
  + exact Hbs.
  + lia.
  + rewrite HLf, HLc. lia.
  + rewrite HLf. lia.
  + lia.
  + reflexivity.
- (* |r'| <= s % 12 : the copy takes what is left *)
  pose proof (w6c7_ltu_f _ (bv_unsigned s0) (Z.of_nat (length rest)) B36 Hbs0 B33 ltac:(lia) ltac:(lia) Hc)
    as HGE.
  assert (Hz0 : (length rest - Z.to_nat (bv_unsigned s0 mod 12))%nat = 0%nat) by lia.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_CPY.
  { apply (w6c7_awr_ok _ _ R F);
    [ rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32
    | vm_compute; reflexivity | lia | lia | exact HFw]. }
  lazymatch type of HS with st_ok _ ?E2 _ _ =>
    assert (F32 : ew E2 32 = Z_to_bv 64 F) by (rewrite ?ew_ewset_other by lia; exact E32);
    assert (F14 : ew E2 14 = Z_to_bv 64 (cur - 1)) by (rewrite ?ew_ewset_other by lia; exact E14);
    assert (F35 : ew E2 35 = Z_to_bv 64 sa) by (rewrite ?ew_ewset_other by lia; exact E35);
    assert (F34 : ew E2 34 = Z_to_bv 64 (bv_unsigned t0)) by (rewrite ?ew_ewset_other by lia; exact E34);
    assert (F36 : ew E2 36 = Z_to_bv 64 (bv_unsigned s0)) by (rewrite ?ew_ewset_other by lia; exact E36);
    assert (F33 : ew E2 33 = Z_to_bv 64 (Z.of_nat (length rest) + 3))
      by (rewrite ?ew_ewset_other by lia; exact E33);
    assert (G9 : bv_unsigned (ew E2 9) = R) by (rewrite ?ew_ewset_other by lia; exact U9);
    assert (G32 : bv_unsigned (ew E2 32) = F) by (rewrite ?ew_ewset_other by lia; exact U32)
  end.
  lazymatch goal with
  | HF1 : frame_of ?E0 ?rs0 (mrestrict _ memc) (mrestrict _ ?m1),
    HF2 : frame_of ?E1 ?rs1 (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (F + 0xf0 <= a < F + 0xf8) ->
      aview rsegs (w_H W) m2 a = aview rsegs (w_H W) memc a)
    by (apply (w6c7_keep1 E1 rs1 R F memc m1 m2 W
          (w6c7_keep1 E0 rs0 R F memc memc m1 W ltac:(intros a Ha X Y; reflexivity) HF1
             ltac:(vm_compute; reflexivity) U9 U32)
          HF2 ltac:(vm_compute; reflexivity) G9 G32))
  end.
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msx HSx eq_refl) at 1 end.
  rewrite w6c7_ent2. cbn [fst snd].
  eapply (w6c7_fin STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa (t0 :: s0 :: rest)
    _ _ _ (bv_unsigned t0 mod 21) (bv_unsigned s0 mod 12)
    (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest) (cur + 2)
    (cur + Z.of_nat (length (t0 :: s0 :: rest) - length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest)))
    (Z.of_nat (length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest)))
    (Ent (bv_unsigned t0 mod 21) (bv_unsigned s0 mod 12)
      (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest
       ++ zeros (Z.to_nat (bv_unsigned s0 mod 12)
                 - length (firstn (Z.to_nat (bv_unsigned s0 mod 12)) rest)))) Hctx Hin).
  + assumption.
  + w6c7_kio.
  + intros rr Hrr.
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (regs_kept_of_st_ok rsegs _ _ msx regs
        (w6c_extra F (Z.of_nat (length rest) + 3) (bv_unsigned t0) sa (bv_unsigned s0)) (w_H W) w6c7_clob HSx
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) rr) end.
    * cbv [w6c_keep In] in Hrr. repeat (destruct Hrr as [<-|Hrr]; [vm_compute; discriminate|]). destruct Hrr.
    * cbv [w6c_keep In] in Hrr.
      repeat (destruct Hrr as [<-|Hrr]; [cbv [w6c7_clob In]; intros X;
        repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hrr.
  + exact KE.
  + w6c7_reg HS (1%bv : bv 5). reflexivity.
  + w6c7_reg HS (10%bv : bv 5).
    rewrite (w6c7_soff _ 32 F 248 F32 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + w6c7_reg HS (11%bv : bv 5).
    rewrite (w6c7_soff _ 14 (cur - 1) 3 F14 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + w6c7_reg HS (12%bv : bv 5).
    etransitivity;
    [ exact (w6c7_soff _ 33 (Z.of_nat (length rest) + 3) (-3) F33 ltac:(lia) ltac:(lia)) |].
    unfold w64; f_equal. rewrite HLf. lia.
  + w6c7_reg HS (20%bv : bv 5).
    rewrite (w6c7_soff _ 35 sa 0 F35 ltac:(lia) ltac:(lia)). unfold w64; f_equal; lia.
  + w6c7_reg HS (25%bv : bv 5).
    etransitivity;
    [ exact (w6c7_add _ (SOff 14 0) (SOff 33 0) (cur - 1 + 0) (Z.of_nat (length rest) + 3 + 0)
        (w6c7_soff _ 14 (cur - 1) 0 F14 ltac:(lia) ltac:(lia))
        (w6c7_soff _ 33 (Z.of_nat (length rest) + 3) 0 F33 ltac:(lia) ltac:(lia))
        ltac:(lia) ltac:(lia) ltac:(lia)) |].
    unfold w64; f_equal. rewrite HLc, HLs, Hz0. lia.
  + lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (w6c7_chunk _ _ msx (w_H W) 1%nat _ 240 4%N w6c_e7t (bv_unsigned t0 mod 21) 32%nat F HSx
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) G32
        ltac:(apply (w6c_t21 _ (bv_unsigned t0) F34); lia)
        ltac:(apply w6c7_w4; lia) ltac:(cbn; lia)) end.
  + lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (w6c7_chunk _ _ msx (w_H W) 1%nat _ 244 4%N w6c_e7s (bv_unsigned s0 mod 12) 32%nat F HSx
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) G32
        ltac:(exact (w6c_s12 _ (bv_unsigned s0) F36 Hbs0))
        ltac:(apply w6c7_w4; lia) ltac:(cbn; lia)) end.
  + assert (Hnl0 : Z.of_nat (length (skipn (Z.to_nat (bv_unsigned s0 mod 12)) rest)) mod 2 ^ 64 = 0)
      by (rewrite HLs, Hz0; reflexivity).
    rewrite Hnl0.
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ =>
      apply (w6c7_chunk _ _ msx (w_H W) 0%nat _ 248 8%N (SLit 0) 0 9%nat R HSx
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(w6c7_in) G9 ltac:(reflexivity)
        ltac:(apply w6c7_w8; lia) ltac:(cbn; lia)) end.
  + exact Hbs.
  + lia.
  + rewrite HLf, HLc. lia.
  + rewrite HLf. lia.
  + lia.
  + reflexivity.
Qed.

(* ===================== the block statement ===================== *)
Theorem w6c_case7 : w6c_case7_stmt B.
Proof.
unfold w6c_case7_stmt, w6c_case_stmt. cbv beta.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa r Hctx Hin.
change (w6c_pc 7) with W6C_D7.
destruct r as [|t0 [|s0 rest]].
- exact (w6c7_case0 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa Hctx Hin).
- exact (w6c7_case1 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa t0 Hctx Hin).
- exact (w6c7_case2 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa t0 s0 rest
    Hctx Hin).
Qed.
End d.
End c.

Print Assumptions w6c_case7.
