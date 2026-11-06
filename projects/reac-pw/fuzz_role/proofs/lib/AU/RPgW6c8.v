(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6c8.v at cb9cdc023f20; image B's case 8:
   its pcs and code table, the registers s2 / s6 / s10 / t1 / s4 / a6, the cells R + 0x130 / R + 0x150, e62 at
   F + 0x210 in the class-4 frame (1024 bytes), the three UBSan trap tests decided by the engine, and s2 / s6 / s10 at
   the entry of __asan_memset. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6c8B.v at 05426fac6916 for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role (lib/AU/Img0.rsegs,
   lib/A/RPgBase and RPgCSpec, lib/AU/RPgMem / RPgSteps / RPgSeg / RPgW6bBase / RPgW6cBase; rtmb_ -> rm_,
   rtsb_ -> rl_); every pc is role B's (the case entry 0x8122c, the stops 0x81284 and 0x812a4, __asan_memset 0x51608)
   and the table t8 is at 0x21140; the registers are role B's (s11 the shadow offset, a6 the kind byte's address
   c - 1, s4 = 1 the left side of the pointer-overflow tests); the cells are [R+0x110] = &e62.body (loaded into a4
   before the first trap test and moved to a0 before the call) and [R+0x158] = &e62; the real frame is 0x200 bytes;
   the input avoids role B's write ranges; the post carries no s10 conjunct (role's case 8 keeps no &e62 in a
   register). *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the block lemma w6cb_h8 of
   lib/AU/RPgW6cBase.v, the head of case 8 of ent_build's `switch (kind % 10)` (pod.h:359-366) inside
   LLVMFuzzerTestOneInput (0x80020), from the case entry 0x8122c to the entry of __asan_memset 0x51608 with
   ra = 0x81584. Proves no function (kind: segment lemma).

   THE CODE (s1 = R, s11 = SHADOW_OFF, s2 = c the cursor, s6 = |r|, a6 = c - 1, t1 = |r| + 1, s4 = 1; every
   `j 0x82604` is a UBSan trap branch to the `unimp`):
     0x8122c  beqz s6 -> 0x8155c                          no byte left
     0x81230  a0 := s2 + 1; 0x81234 a4 := [R+0x110]; 0x81238 bltu s4,a0 (the trap at 0x8123c when not taken)
     0x81240 .. 0x8124c  the instrumented check of s2 (slow block 0x81a7c); 0x81250 lbu a1,0(s2) (= t)
     0x81254 .. 0x81260  a0 := 0x21140; a1 := t & 3; a2 := 4 (t & 3); 0x81264 a3 := ~a0; 0x81268 bgeu a3,a2
     0x81270 .. 0x81280  a0 := a0 + a2 and its instrumented check, 4 bytes (slow block 0x81a88)
     0x81284  lw a0,0(a0); s6 := t1 - 2; s2 := a6 + 2; a2 := [R+0x158]; e62.type := a0; a0 := 3
     0x8129c  beq a1,a0 -> 0x81330 (a String); 0x812a0 beqz s6 -> 0x81330 (no second byte)
     0x812a4  a0 := s2 + 1; 0x812a8 bltu s4,a0
     0x812b0 .. 0x812bc  the instrumented check of s2 (slow block 0x81b2c); 0x812c0 lbu a2,0(s2) (= s);
              s6 := t1 - 3; s2 := a6 + 3; a2 := s & 3; -> 0x81570
     0x81330  a2 := 0; -> 0x81570
     0x8155c  a2 := 0; a0 := [R+0x158]; e62.type := 4; a4 := [R+0x110]
     0x81570  a0 := [R+0x158]; e62.size := a2; a0 := a4; a1 := 0; 0x81580 jal __asan_memset
   THE PROOF. Four arms, one lemma each, joined by w6cb_h8 after a split on r and on t & 3: w8_p0 (no byte), w8_p1s
   (t & 3 = 3, a String), w8_p1n (one byte, t & 3 <> 3), w8_p2 (two bytes or more, t & 3 <> 3). An arm is one to three
   runs of the token engine (lib/Reusable/YCbq.v aj_run_to_tok, which follows each slow block itself and leaves one
   range_addressable obligation per instrumented check) over one symbolic state. Its environment is the entry's
   registers and six extra atoms (w8_extra: 32 = F, 33 = t, 34 = s, 35 = &t8[t & 3], 36 = t8[t & 3], 37 = t mod 4);
   s2 is pinned to a6 + 1 and s4 to the literal 1, so every cursor address is based at one atom (a6's) and the engine
   decides the trap tests `bltu s4,a0` (a0 = a6 + 2 or a6 + 3, at least 3) and `bgeu ~0x21140, 4 (t & 3)` from the
   atom facts. The regions: the cells [R+0x110] and [R+0x158] (w8_RA, w8_RB), e62's header (w8_RE, the only write
   window, in the frame (4, pos)) and the first input byte (w8_RI). At 0x81284 a0 is pinned to atom 35 and a1 to
   atom 37 (to 3 for a String), so the engine decides both branches from the facts; the input byte's region goes out
   and the table entry's (w8_RT, image bytes) comes in, because the input may lie anywhere the contract allows (the
   contract does not keep it off .rodata). At 0x812a4 the table entry goes out and the second byte (w8_RS) comes in.
   The facts keep e62's window apart from the shadow band the checks read: F lies in the low or in the high
   application memory (w8_hi_of), and each arm runs once per side (destruct hi).
   THE TRAPS AND ERROR PATHS, each refuted: the trap branches 0x81238 / 0x812a8 (`bltu s4,a0`, to the `j 0x82604` at
   0x8123c / 0x812ac) are decided by the engine from s4 = 1 and a6's fact (a6 >= 1); the trap branch 0x81268
   (`bgeu a3,a2`, to 0x8126c) is decided from t's fact (4 (t & 3) <= 12); the error-path jumps 0x81a84 (the check
   of s2 at 0x81240), 0x81a94 (the check of t8[t & 3] at 0x81274) and 0x81b34 (the check of s2 at 0x812b0) are not
   reached because each check passes: the engine's obligation range_addressable is discharged by w8_obl_cur from the
   input's range (w6cb_in) and by w8_obl_tbl from the table's range (the statement's premise). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YP08 YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgMem RPgSteps RPgSeg RPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW6cBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition W8_U : Z := 0x81284.
Definition W8_V : Z := 0x812a4.
Definition w8_extra (F t s : Z) : list word :=
  [w64 F; w64 t; w64 s; w64 (W6CB_T8 + 4 * (t mod 4)); w64 (w6cb_ty8 t); w64 (t mod 4)].
Definition w8_RA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x110 0x118 0 0 [YP09.mkChunk 0x110 (CVal 8 (SOff 32 0x218))].
Definition w8_RB : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x158 0x160 0 0 [YP09.mkChunk 0x158 (CVal 8 (SOff 32 0x210))].
Definition w8_RE : YP09.region := YP09.mkRegion (Some 32%nat) 0x210 0x218 0x210 0x218 [].
Definition w8_RI : YP09.region := YP09.mkRegion (Some 16%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 33 0))].
Definition w8_RS : YP09.region := YP09.mkRegion (Some 16%nat) 2 3 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 34 0))].
Definition w8_RT : YP09.region := YP09.mkRegion (Some 35%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))].
Definition w8_regs (m : bool) : smem := if m then [w8_RA; w8_RB; w8_RE; w8_RI] else [w8_RA; w8_RB; w8_RE].
Definition w8_Flo (hi : bool) : Z := if hi then kHighMemBeg else 4096.
Definition w8_Fhi (hi : bool) : Z := if hi then 2 ^ 47 - 1024 else kLowShadowBeg - 1024.
Definition w8_G (hi : bool) (a4hi nlo nhi ulo uhi : Z) : facts :=
  mkFacts [(27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (9%nat, mkAF kHighMemBeg (2 ^ 47) 4);
           (32%nat, mkAF (w8_Flo hi) (w8_Fhi hi) 5); (16%nat, mkAF 1 a4hi 0);
           (22%nat, mkAF nlo nhi 0); (6%nat, mkAF (nlo + 1) (nhi + 1) 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF W6CB_T8 (W6CB_T8 + 12) 2);
           (36%nat, mkAF 2 8 1); (37%nat, mkAF ulo uhi 0)] [] [].
Definition w8_Bx : sv := SOff 27 0.
Definition w8_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma w8_af : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof. intros E n v lo hi al H Hv Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia. auto. Qed.

Lemma w8_ty8_in : forall t, In (w6cb_ty8 t) [4; 6; 2; 8].
Proof.
intros t. unfold w6cb_ty8. pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as H.
assert (E : t mod 4 = 0 \/ t mod 4 = 1 \/ t mod 4 = 2 \/ t mod 4 = 3) by lia.
destruct E as [E|[E|[E|E]]]; rewrite E; cbn; tauto.
Qed.

Lemma w8_G_ok : forall regs F t s R c n hi a4hi nlo nhi ulo uhi,
  getr regs 27 = w64 SHADOW_OFF -> getr regs 9 = w64 R -> getr regs 16 = w64 (c - 1) ->
  getr regs 22 = w64 n -> getr regs 6 = w64 (n + 1) ->
  kHighMemBeg <= R <= 2 ^ 47 -> R mod 16 = 0 ->
  w8_Flo hi <= F <= w8_Fhi hi -> F mod 32 = 0 ->
  1 <= c - 1 <= a4hi -> a4hi < 2 ^ 64 -> nlo <= n <= nhi -> 0 <= nlo -> nhi + 1 < 2 ^ 64 ->
  0 <= t < 256 -> 0 <= s < 256 -> ulo <= t mod 4 <= uhi ->
  facts_ok (Ereg regs (w8_extra F t s)) (w8_G hi a4hi nlo nhi ulo uhi).
Proof.
intros regs F t s R c n hi a4hi nlo nhi ulo uhi H27 H9 H16 H22 H6 HR HR16 HF HF32 Hc Ha4 Hn Hnlo Hnhi Ht Hs Hu.
assert (HFb : 0 <= F < 2 ^ 47) by (destruct hi; unfold w8_Flo, w8_Fhi, kHighMemBeg, kLowShadowBeg in HF; lia).
pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as Htm.
unfold facts_ok, w8_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; exact I].
split; [apply (w8_af _ _ SHADOW_OFF); [rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27 | unfold SHADOW_OFF; lia | lia | reflexivity | lia]|].
split; [apply (w8_af _ _ R); [rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9 | unfold kHighMemBeg in HR; lia | lia | exact HR16 | lia]|].
split; [apply (w8_af _ _ F); [exact (ew_Ereg_extra regs _ 0) | lia | lia | exact HF32 | lia]|].
split; [apply (w8_af _ _ (c - 1)); [rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
split; [apply (w8_af _ _ n); [rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
split; [apply (w8_af _ _ (n + 1)); [rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
split; [apply (w8_af _ _ t); [exact (ew_Ereg_extra regs _ 1) | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
split; [apply (w8_af _ _ s); [exact (ew_Ereg_extra regs _ 2) | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
split; [apply (w8_af _ _ (W6CB_T8 + 4 * (t mod 4))); [exact (ew_Ereg_extra regs _ 3) | unfold W6CB_T8; lia | unfold W6CB_T8; lia
  | change (2 ^ 2) with 4; rewrite (Z.mul_comm 4), Z.mod_add by lia; reflexivity | lia]|].
split; [apply (w8_af _ _ (w6cb_ty8 t)); [exact (ew_Ereg_extra regs _ 4) | | | | lia];
  pose proof (w8_ty8_in t) as Hin; cbn [In] in Hin; destruct Hin as [E|[E|[E|[E|[]]]]]; rewrite <- E; first [lia | reflexivity]|].
split; [apply (w8_af _ _ (t mod 4)); [exact (ew_Ereg_extra regs _ 5) | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
exact I.
Qed.

Lemma w8_den_off : forall E n c v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> x = v + c ->
  sv_denot E (SOff n c) = w64 x.
Proof.
intros E n c v x H Hv Hc ->. apply bv_eq. rewrite denot_SOff, H. unfold w64. rewrite !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma w8_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R F c t s (m : bool) G,
  getr regs 9 = w64 R -> getr regs 16 = w64 (c - 1) ->
  kHighMemBeg <= R -> R + 0x200 <= 2 ^ 47 -> 4096 <= F -> F + 1024 <= R ->
  1 <= c - 1 -> c + 1 <= 2 ^ 47 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 (F + 0x210) ->
  (forall o, 0x210 <= o < 0x218 -> apresent (w_H W) memc (F + o)) ->
  (m = true -> val_mem rsegs (mrestrict (w_H W) memc) (c - 1 + 1) 1 t /\ 0 <= t < 256 /\
     ~ (R + 0x48 <= c < R + 0x160) /\ ~ (F + 0x20 <= c < F + 0x278)) ->
  facts_ok (Ereg regs (w8_extra F t s)) G ->
  st_ok rsegs (Ereg regs (w8_extra F t s)) (mkSS W6CB_D8 sr_atoms (w8_regs m) None G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6CB_D8) memc (seg_rom rsegs))).
Proof.
intros W regs memc R F c t s m G H9 H16 HR0 HR1 HF0 HFR Hc0 Hc1 V110 V158 HpE Hin HG.
set (E := Ereg regs (w8_extra F t s)).
assert (U9 : bv_unsigned (ew E 9) = R)
  by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; unfold kHighMemBeg in HR0; lia).
assert (E32 : ew E 32 = Z_to_bv 64 F) by exact (ew_Ereg_extra regs _ 0).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; unfold kHighMemBeg in HR0; lia).
assert (U16 : bv_unsigned (ew E 16) = c - 1)
  by (subst E; rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl), H16; unfold w64; apply unsigned_lit_small; lia).
assert (RA : region_ok rsegs E (mrestrict (w_H W) memc) w8_RA).
{ unfold w8_RA. apply (rm_ro_region rsegs E (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
  constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ R 0x110 8 (SOff 32 0x218) (F + 0x218)); [| cbn; lia | cbn; lia | exact V110].
  apply (w8_den_off _ _ _ F); [exact E32 | lia | lia | reflexivity]. }
assert (RB : region_ok rsegs E (mrestrict (w_H W) memc) w8_RB).
{ unfold w8_RB. apply (rm_ro_region rsegs E (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
  constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ R 0x158 8 (SOff 32 0x210) (F + 0x210)); [| cbn; lia | cbn; lia | exact V158].
  apply (w8_den_off _ _ _ F); [exact E32 | lia | lia | reflexivity]. }
assert (RE : region_ok rsegs E (mrestrict (w_H W) memc) w8_RE).
{ unfold w8_RE. apply (rm_rw_region rsegs E (w_H W) memc 32%nat F); [exact U32 | lia | lia | | constructor].
  intros o Ho. apply HpE. exact Ho. }
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- destruct m; vm_compute; reflexivity.
- destruct m; unfold w8_regs.
  + destruct (Hin eq_refl) as (V1 & Ht & D1 & D3).
    constructor; [exact RA|]. constructor; [exact RB|]. constructor; [exact RE|]. constructor; [|constructor].
    unfold w8_RI. apply (rm_ro_region rsegs E (w_H W) memc 16%nat (c - 1)); [exact U16 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ (c - 1) 1 1 (SOff 33 0) t); [| cbn; lia | cbn; lia | exact V1].
    apply (w8_den_off _ _ _ t); [exact (ew_Ereg_extra regs _ 1) | lia | lia | lia].
  + constructor; [exact RA|]. constructor; [exact RB|]. constructor; [exact RE | constructor].
- destruct m.
  + destruct (Hin eq_refl) as (V1 & Ht & D1 & D3).
    unfold w8_regs, w8_RA, w8_RB, w8_RE, w8_RI. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U32, U16.
    repeat split; lia.
  + unfold w8_regs, w8_RA, w8_RB, w8_RE. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U32.
    repeat split; lia.
- exact HG.
Qed.

(* ---- an sv over one atom, its value checked for every value the atom may hold ---- *)
Fixpoint w8_uses (P : nat -> bool) (v : sv) : bool :=
match v with
| SLit _ => true
| SOff n _ => P n
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => w8_uses P a && w8_uses P b
| SExt _ _ a => w8_uses P a
| SData _ _ _ => false
| SF1 _ a => w8_uses P a
| SF2 _ a b => w8_uses P a && w8_uses P b
| SF3 _ a b c => w8_uses P a && w8_uses P b && w8_uses P c
end.
Lemma w8_denot_agree : forall P E E' v, w8_uses P v = true -> (forall n, P n = true -> ew E n = ew E' n) ->
  sv_denot E v = sv_denot E' v.
Proof.
intros P E E' v Hv HE. induction v; cbn in *; try discriminate;
try (apply andb_prop in Hv as [Ha Hb]; rewrite (IHv1 Ha), (IHv2 Hb); reflexivity).
- reflexivity.
- rewrite (HE n Hv). reflexivity.
- rewrite (IHv Hv). reflexivity.
- rewrite (IHv Hv). reflexivity.
- apply andb_prop in Hv as [Hab Hc]. apply andb_prop in Hab as [Ha Hb].
  rewrite (IHv1 Ha), (IHv2 Hb), (IHv3 Hc). reflexivity.
Qed.
Definition w8_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma w8_chk : forall (X : sv) (n : nat) (vals : list Z) (g : Z -> Z) E v,
  w8_uses (fun i => Nat.eqb i n) X = true ->
  forallb (fun v => bv_unsigned (sv_denot (w8_envz v) X) =? bv_unsigned (Z_to_bv 64 (g v))) vals = true ->
  ew E n = Z_to_bv 64 v -> In v vals -> sv_denot E X = Z_to_bv 64 (g v).
Proof.
intros X n vals g E v Hu Hc He Hin.
rewrite (w8_denot_agree (fun i => Nat.eqb i n) E (w8_envz v) X Hu).
- apply bv_eq. apply Z.eqb_eq. exact (proj1 (forallb_forall _ _) Hc v Hin).
- intros i Hi. apply Nat.eqb_eq in Hi. subst i. rewrite He. reflexivity.
Qed.
Lemma w8_in256 : forall t, 0 <= t < 256 -> In t (map Z.of_nat (seq 0 256)).
Proof. intros t Ht. apply in_map_iff. exists (Z.to_nat t). split; [lia | apply in_seq; lia]. Qed.

(* ---- a chunk of region i of a run's state, at its absolute address ---- *)
Lemma w8_val_at : forall E ss H ms i r off (n : N) e v a,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  a = base_val E (YP09.r_base r) + off ->
  val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss H ms i r off n e v a HS Hi Hc He Hv Hn ->.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hi)).
pose proof (YP09.region_ok_chunk rsegs E _ r _ Hok Hc) as Hck.
exact (val_of_chunk_ok rsegs E _ _ off n e v Hck He Hv Hn).
Qed.

(* ---- the bytes a run keeps: everything outside e62's header ---- *)
Lemma w8_keep_step : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) F,
  (forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/ (YP09.r_base r = Some 32%nat /\ bv_unsigned (ew E 32) = F /\
    0x210 <= YP09.r_wlo r /\ YP09.r_whi r <= 0x218)) rs ->
  forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros E rs H m0 m1 m2 F K HF Hw a Ha Hn. rewrite <- (K a Ha Hn).
apply (aview_eq_of rsegs). apply HF. rewrite unsigned_lit_small by exact Ha.
intros (r & Hin & Hr). rewrite Forall_forall in Hw. destruct (Hw r Hin) as [Hw0 | (Hb & H32 & Hlo & Hhi)]; [lia|].
apply Hn. unfold w6cb_hdr_wr. rewrite Hb in Hr. cbn [base_val] in Hr. rewrite H32 in Hr. lia.
Qed.
Lemma w8_ra_kept : forall H (m m' : word -> option byte) Bs a n,
  range_addressable (aview rsegs H m) Bs a n ->
  (forall x, a <= x < a + n -> aview rsegs H m' (shadow_of_addr Bs x) = aview rsegs H m (shadow_of_addr Bs x)) ->
  range_addressable (aview rsegs H m') Bs a n.
Proof. intros H m m' Bs a n Hr K x Hx. destruct (Hr x Hx) as (s & Hs & Ho). exists s. rewrite K by exact Hx. auto. Qed.

(* ---- dropping a region of a symbolic state ---- *)
Lemma w8_regions_wf_app : forall l1 l2, regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. intros l1 l2. induction l1 as [|r l1 IH]; [reflexivity|]. cbn [app regions_wf]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma w8_all_disj_drop : forall E a l1 r l2, all_disjoint E a (l1 ++ r :: l2) -> all_disjoint E a (l1 ++ l2).
Proof.
intros E a l1 r l2. induction l1 as [|x l1 IH]; cbn [app all_disjoint]; [intros [_ H]; exact H|].
intros [H1 H2]. split; [exact H1 | exact (IH H2)].
Qed.
Lemma w8_pw_disj_drop : forall E l1 r l2, pairwise_disjoint E (l1 ++ r :: l2) -> pairwise_disjoint E (l1 ++ l2).
Proof.
intros E l1 r l2. induction l1 as [|x l1 IH]; cbn [app pairwise_disjoint]; [intros [_ H]; exact H|].
intros [H1 H2]. split; [exact (w8_all_disj_drop E x l1 r l2 H1) | exact (IH H2)].
Qed.
Lemma w8_st_ok_drop : forall E pc rg fr l1 r l2 resv f ms,
  st_ok rsegs E (mkSST pc rg fr (l1 ++ r :: l2) resv f) ms -> st_ok rsegs E (mkSST pc rg fr (l1 ++ l2) resv f) ms.
Proof.
intros E pc rg fr l1 r l2 resv f ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpw) & H9).
repeat (split; [assumption|]). split; [|exact H9]. cbn [ss_mem] in *.
split; [|split].
- rewrite w8_regions_wf_app in *. cbn [regions_wf] in Hwf.
  apply andb_true_iff in Hwf as [Ha Hb]. apply andb_true_iff in Hb as [_ Hb]. rewrite Ha, Hb. reflexivity.
- apply Forall_app in Hok as [Ha Hb]. inversion Hb; subst. apply Forall_app. split; assumption.
- exact (w8_pw_disj_drop E l1 r l2 Hpw).
Qed.

(* ---- the table t8 at 0x21140: four 4-byte entries {4, 6, 2, 8}, read-only image bytes ---- *)
Definition w8_tbl_ok : bool :=
  forallb (fun i => forallb (fun k =>
    in_rom_b (W6CB_T8 + 4 * Z.of_nat i + Z.of_nat k) && YP08.img_byte_ok rsegs (W6CB_T8 + 4 * Z.of_nat i + Z.of_nat k) &&
    match img_byte rsegs (W6CB_T8 + 4 * Z.of_nat i + Z.of_nat k) with
    | Some b => bv_unsigned b =? YO0f.le_byte (nth i Tables.t8 0) 4 k
    | None => false
    end) (seq 0 4)) (seq 0 4).
Lemma w8_tbl_ok_true : w8_tbl_ok = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w8_tbl_val : forall (W : world rsegs) mem t, rom_view rsegs W mem -> 0 <= t ->
  val_mem rsegs (mrestrict (w_H W) mem) (W6CB_T8 + 4 * (t mod 4)) 4 (w6cb_ty8 t).
Proof.
intros W mem t HR Ht k Hk.
pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as Hm.
pose proof (proj1 (forallb_forall _ _) w8_tbl_ok_true (Z.to_nat (t mod 4)) ltac:(apply in_seq; lia)) as H1.
pose proof (proj1 (forallb_forall _ _) H1 k ltac:(apply in_seq; lia)) as H2. cbv beta in H2.
rewrite Z2Nat.id in H2 by lia.
apply andb_prop in H2 as [H2 H4]. apply andb_prop in H2 as [H2 H3].
destruct (mbyte_rom W mem _ HR H2 H3) as (b & Hb & Hmb).
rewrite Hmb. rewrite Hb in H4. apply Z.eqb_eq in H4. unfold w6cb_ty8. rewrite <- H4. f_equal. symmetry.
apply Z_to_bv_bv_unsigned.
Qed.
Definition w8_img_b (a : Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs.
Lemma w8_tbl_img : forall a, W6CB_T8 <= a < W6CB_T8 + 16 -> YG0d.in_img rsegs a.
Proof.
intros a Ha.
assert (Hc : forallb w8_img_b (map (fun i => W6CB_T8 + Z.of_nat i) (seq 0 16)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hc.
assert (Hb : w8_img_b a = true).
{ replace a with (W6CB_T8 + Z.of_nat (Z.to_nat (a - W6CB_T8))) by lia. apply Hc. apply in_map_iff.
  exists (Z.to_nat (a - W6CB_T8)). split; [reflexivity | apply in_seq; lia]. }
unfold w8_img_b in Hb. apply existsb_exists in Hb as (sg & Hin & Hb). apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2. exists sg. split; [exact Hin | lia].
Qed.

Ltac w8_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; w8_kio].

(* ---- the regions added in the middle of the head: the table entry, the second input byte ---- *)
Lemma w8_RT_ok : forall E (W : world rsegs) mem m0 F t,
  ew E 35 = Z_to_bv 64 (W6CB_T8 + 4 * (t mod 4)) -> ew E 36 = Z_to_bv 64 (w6cb_ty8 t) -> 0 <= t ->
  rom_view rsegs W m0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) mem a = aview rsegs (w_H W) m0 a) ->
  (forall a, W6CB_T8 <= a < W6CB_T8 + 16 -> ~ (F <= a < F + 1024)) ->
  region_ok rsegs E (mrestrict (w_H W) mem) w8_RT.
Proof.
intros E W mem m0 F t E35 E36 Ht HR KE HTF. pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as Hm.
pose proof (w8_ty8_in t) as Hty. assert (Hv : 2 <= w6cb_ty8 t <= 8) by (cbn [In] in Hty; lia).
unfold w8_RT. apply (rm_ro_region rsegs E (w_H W) mem 35%nat (W6CB_T8 + 4 * (t mod 4))).
- rewrite E35. apply unsigned_lit_small. unfold W6CB_T8; lia.
- unfold W6CB_T8; lia.
- unfold W6CB_T8; lia.
- constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ _ 0 4 (SOff 36 0) (w6cb_ty8 t)).
  + apply (w8_den_off _ _ _ (w6cb_ty8 t)); [exact E36 | lia | lia | lia].
  + change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  + cbn. lia.
  + rewrite Z.add_0_r. change (N.to_nat 4) with 4%nat. apply (rl_val_kept (w_H W) m0 mem).
    * intros k Hk. apply KE; [unfold W6CB_T8; lia|]. unfold w6cb_hdr_wr. intros Hw.
      apply (HTF (W6CB_T8 + 4 * (t mod 4) + k)); lia.
    * exact (w8_tbl_val W m0 t HR Ht).
Qed.
Lemma w8_RS_ok : forall E (W : world rsegs) mem m0 F c s,
  ew E 16 = Z_to_bv 64 (c - 1) -> ew E 34 = Z_to_bv 64 s -> 1 <= c - 1 -> c + 2 <= 2 ^ 64 -> 0 <= s < 256 ->
  val_mem rsegs (mrestrict (w_H W) m0) (c - 1 + 2) 1 s ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) mem a = aview rsegs (w_H W) m0 a) ->
  ~ w6cb_hdr_wr F (c + 1) ->
  region_ok rsegs E (mrestrict (w_H W) mem) w8_RS.
Proof.
intros E W mem m0 F c s E16 E34 Hc0 Hc1 Hs V2 KE Hn.
unfold w8_RS. apply (rm_ro_region rsegs E (w_H W) mem 16%nat (c - 1)).
- rewrite E16. apply unsigned_lit_small. lia.
- lia.
- lia.
- constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ _ 2 1 (SOff 34 0) s).
  + apply (w8_den_off _ _ _ s); [exact E34 | lia | lia | lia].
  + cbn. lia.
  + cbn. lia.
  + change (N.to_nat 1) with 1%nat. apply (rl_val_kept (w_H W) m0 mem); [|exact V2].
    intros k Hk. cbn in Hk. replace (c - 1 + 2 + k) with (c + 1) by lia. apply KE; [lia | exact Hn].
Qed.

(* a register pinned to another sv of the same value *)
Lemma w8_pin_eq : forall E ss ms (r : bv 5) e e' v, st_ok rsegs E ss ms -> sr_get (ss_regs ss) r = e' ->
  sv_denot E e = Z_to_bv 64 v -> sv_denot E e' = Z_to_bv 64 v -> bv_eqb r 0 = false ->
  st_ok rsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e e' v HS Hr He He' H0. apply (st_ok_pin_sv rsegs E ss ms r e HS H0).
rewrite (st_ok_reg rsegs E ss ms r HS), Hr, He, He'. reflexivity.
Qed.
(* the index of e62's region (based at atom 32) in a state's regions *)
Fixpoint w8_find32 (l : smem) (i : nat) : nat :=
match l with
| [] => i
| r :: l' => match YP09.r_base r with Some 32%nat => i | _ => w8_find32 l' (S i) end
end.

(* ---- tactics ---- *)
(* an atom of a run's environment (the entry's, with the token atoms of the runs set above it) *)
Ltac w8_ew H := repeat (rewrite ew_ewset_other by lia); exact H.
Ltac w8_strip := repeat (rewrite ew_ewset_other by lia).
(* the regions' write windows: none but e62's header *)
Ltac w8_win E32 :=
  lazymatch goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end;
  repeat (apply Forall_cons;
    [ cbv beta; first
      [ left; cbn; lia
      | right; cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; split; [reflexivity|];
        split; [w8_strip; rewrite E32; apply unsigned_lit_small; lia | lia] ]
    |]);
  apply Forall_nil.
(* after a run: the bytes kept outside e62's header, the old machine states cleared *)
Ltac w8_keep E32 :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _),
                      KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr _ a -> _ |- _ =>
    let KS := fresh "KS" in let HW := fresh "HW" in
    pose proof (w8_keep_step _ _ _ _ _ _ _ KE HFr) as KS;
    lazymatch type of KS with ?P -> _ => assert (HW : P) by (w8_win E32) end;
    specialize (KS HW); clear HW KE HFr; rename KS into KE
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with old : machine_state |- _ => clear old end.
(* the write rights: e62's header in the frame (4, pos), every other region read-only *)
Ltac w8_awr E32 pos Hown HF :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?ly ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc ly ow) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (rl_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0);
      [ reflexivity | w8_strip; rewrite E32, <- HF, unsigned_lit_small by lia; lia
      | exact Hown | cbn; lia | cbn; lia | ] ].
(* the shadow base of a check *)
Ltac w8_ubx E27 := unfold w8_Bx; apply (U_atom _ 27 SHADOW_OFF); [w8_ew E27 | unfold SHADOW_OFF; lia].
(* the check of the cursor s2 = a6 + k *)
Ltac w8_obl_cur E27 E16 Hra a4 :=
  apply (obl_of_range rsegs _ _ _ _ _ _ _ _ Hra);
  [ w8_ubx E27
  | rewrite (U_atom_off _ 16 a4) by (first [w8_ew E16 | lia]); lia
  | rewrite (U_atom_off _ 16 a4) by (first [w8_ew E16 | lia]); lia ].
(* the check of the table entry t8[t & 3] *)
Ltac w8_obl_tbl E27 E33 Hra8 t :=
  apply (obl_of_range rsegs _ _ _ _ _ _ W6CB_T8 16 Hra8);
  [ w8_ubx E27 | | ];
  lazymatch goal with |- context [U ?E ?X] =>
    let HU := fresh "HU" in
    assert (HU : sv_denot E X = Z_to_bv 64 (W6CB_T8 + 4 * (t mod 4)))
      by (apply (w8_chk X 33 (map Z.of_nat (seq 0 256)) (fun v => W6CB_T8 + 4 * (v mod 4)));
          [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E33 | apply w8_in256; lia]);
    pose proof (Z.mod_pos_bound t 4 ltac:(lia));
    unfold U; rewrite HU, unsigned_lit_small by (unfold W6CB_T8; lia); lia
  end.
(* a register pinned to e, of value v (tac1: e's value, tac2: the register's) *)
Ltac w8_pin r e v tac1 tac2 :=
  lazymatch goal with HS : st_ok _ ?E ?ss ?ms |- _ =>
    let e' := eval vm_compute in (sr_get (ss_regs ss) r) in
    let HS' := fresh "HS" in
    pose proof (w8_pin_eq E ss ms r e e' v HS ltac:(vm_compute; reflexivity) ltac:(tac1) ltac:(tac2) eq_refl) as HS';
    clear HS; rename HS' into HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS
  end.
(* drop region i *)
Ltac w8_drop i :=
  lazymatch goal with HS : st_ok _ ?E (mkSST ?pc ?rg ?fr ?mm ?rv ?ff) ?ms |- _ =>
    let l1 := eval vm_compute in (firstn i mm) in
    let l2 := eval vm_compute in (skipn (S i) mm) in
    lazymatch eval vm_compute in (nth_error mm i) with Some ?r =>
      let HS' := fresh "HS" in
      pose proof (w8_st_ok_drop E pc rg fr l1 r l2 rv ff ms HS) as HS';
      clear HS; rename HS' into HS; cbn [app] in HS
    end
  end.
(* add region r (okt: its region_ok, disj: apart from the others) *)
Ltac w8_add r okt disj :=
  lazymatch goal with HS : st_ok _ ?E ?ss ?ms |- _ =>
    let HS' := fresh "HS" in
    pose proof (YN2j.st_ok_add_region rsegs E ss ms r HS ltac:(vm_compute; reflexivity) ltac:(okt) ltac:(disj)) as HS';
    clear HS; rename HS' into HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS
  end.
(* a register of the final state, as its sv's value *)
Ltac w8_reg HS r :=
  lazymatch type of HS with st_ok _ ?E ?ssf (restrict _ ?ms) =>
    rewrite (st_ok_restrict_reg rsegs _ E ssf ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssf) r) in
    replace (sr_get (ss_regs ssf) r) with e by (vm_compute; reflexivity)
  end.
(* a 4-byte field of e62 in the final state, from its chunk (tacv: the chunk's value) *)
Ltac w8_eval HS off tacv E32 :=
  lazymatch type of HS with st_ok _ ?E ?ssf (restrict ?H ?ms) =>
    let i := eval vm_compute in (w8_find32 (ss_mem ssf) 0%nat) in
    lazymatch eval vm_compute in (nth_error (ss_mem ssf) i) with Some ?rg =>
      lazymatch eval vm_compute in (find (fun ch => YP09.c_off ch =? off) (YP09.r_chunks rg)) with
      | Some (YP09.mkChunk _ (CVal ?nn ?e)) =>
        eapply (w8_val_at E ssf H ms i rg off nn e _ _ HS eq_refl);
        [ cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
        | tacv
        | lazymatch goal with |- 0 <= _ < ?p => let p' := eval vm_compute in p in change p with p' end; lia
        | cbn; lia
        | cbn [base_val YP09.r_base]; w8_strip; rewrite E32, unsigned_lit_small by lia; lia ]
      end
    end
  end.

(* what a head ends with: ra = 0x81584, a0 = &e62.body, a1 = 0, a2 = sz, s2 = cur, s6 = nl, e62.type = ty,
   e62.size = sz *)
Definition w8_Q (W : world rsegs) (F ty sz nl cur : Z) : bvmap 5 word -> (word -> option byte) -> Prop :=
fun regs2 mem2 =>
 getr regs2 1 = w64 W6CB_RSET /\ getr regs2 10 = w64 (F + 0x218) /\ getr regs2 11 = w64 0 /\
 getr regs2 12 = w64 sz /\ getr regs2 18 = w64 cur /\ getr regs2 22 = w64 nl /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x210) 4 ty /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x214) 4 sz.

(* the end of a head: the memset's entry, its registers and e62's header (ta2 ts2 ts6: a2, s2, s6; tty tsz: the
   chunks of e62.type and e62.size) *)
Ltac w8_leaf F HAE pins pinsok ta2 ts2 ts6 tty tsz E32 :=
  lazymatch goal with HS : st_ok _ ?E ?ssf (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) _ =>
    apply SRr_ret; unfold w6cb_hpost; exists (ms_regs ms), (ms_mem ms), md;
    split; [reflexivity|];
    split; [unfold cfg_at; rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
    split; [assumption|];
    split; [w8_kio|];
    split; [lazymatch type of HAE with env_agree _ (Ereg ?rg ?ex) _ =>
              apply (regs_kept_of_st_ok_pins rsegs E ssf ms rg ex (w_H W) w6cb_clob8 pins HS);
              [env_agree_chain HAE | pinsok | vm_compute; reflexivity] end|];
    split; [assumption|];
    unfold w8_Q;
    split; [w8_reg HS (1%bv : bv 5); reflexivity|];
    split; [w8_reg HS (10%bv : bv 5); apply (w8_den_off _ _ _ F); [w8_ew E32 | lia | lia | reflexivity]|];
    split; [w8_reg HS (11%bv : bv 5); reflexivity|];
    split; [w8_reg HS (12%bv : bv 5); ta2|];
    split; [w8_reg HS (18%bv : bv 5); ts2|];
    split; [w8_reg HS (22%bv : bv 5); ts6|];
    split; [w8_eval HS 528 tty E32 | w8_eval HS 532 tsz E32]
  end.

(* the atoms of the entry's environment *)
Lemma w8_ef : forall (regs : bvmap 5 word) F t s R c n,
  getr regs 9 = w64 R -> getr regs 16 = w64 (c - 1) -> getr regs 6 = w64 (n + 1) -> getr regs 27 = w64 SHADOW_OFF ->
  ew (Ereg regs (w8_extra F t s)) 9 = Z_to_bv 64 R /\ ew (Ereg regs (w8_extra F t s)) 16 = Z_to_bv 64 (c - 1) /\
  ew (Ereg regs (w8_extra F t s)) 6 = Z_to_bv 64 (n + 1) /\ ew (Ereg regs (w8_extra F t s)) 27 = Z_to_bv 64 SHADOW_OFF /\
  ew (Ereg regs (w8_extra F t s)) 32 = Z_to_bv 64 F /\ ew (Ereg regs (w8_extra F t s)) 33 = Z_to_bv 64 t /\
  ew (Ereg regs (w8_extra F t s)) 34 = Z_to_bv 64 s /\
  ew (Ereg regs (w8_extra F t s)) 35 = Z_to_bv 64 (W6CB_T8 + 4 * (t mod 4)) /\
  ew (Ereg regs (w8_extra F t s)) 36 = Z_to_bv 64 (w6cb_ty8 t) /\ ew (Ereg regs (w8_extra F t s)) 37 = Z_to_bv 64 (t mod 4).
Proof.
intros regs F t s R c n H9 H16 H6 H27.
split; [rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9|].
split; [rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16|].
split; [rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6|].
split; [rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27|].
split; [exact (ew_Ereg_extra regs _ 0)|]. split; [exact (ew_Ereg_extra regs _ 1)|].
split; [exact (ew_Ereg_extra regs _ 2)|]. split; [exact (ew_Ereg_extra regs _ 3)|].
split; [exact (ew_Ereg_extra regs _ 4) | exact (ew_Ereg_extra regs _ 5)].
Qed.

Lemma w8_hi_of : forall F, in_app F 1024 -> exists hi, w8_Flo hi <= F <= w8_Fhi hi.
Proof.
intros F (H1 & [H2 | (H2 & H3)]).
- exists false. unfold w8_Flo, w8_Fhi. lia.
- exists true. unfold w8_Flo, w8_Fhi. pose proof YM05.alloc_ceiling_lt. unfold ASAN_CEIL in H3. lia.
Qed.
Lemma w8_ty8_str : forall t, (w6cb_ty8 t =? POD_STRING) = (t mod 4 =? 3).
Proof.
intros t. unfold w6cb_ty8. pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as H.
assert (E : t mod 4 = 0 \/ t mod 4 = 1 \/ t mod 4 = 2 \/ t mod 4 = 3) by lia.
destruct E as [E|[E|[E|E]]]; rewrite E; reflexivity.
Qed.

Section d.
Variable B : asyms.

Lemma w8_hpost_mono : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs pc clob Wr cfg
  (Q1 Q2 : bvmap 5 word -> (word -> option byte) -> Prop),
  SRr rsegs W cfg (w6cb_hpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs pc clob Wr Q1) ->
  (forall regs2 mem2, Q1 regs2 mem2 -> Q2 regs2 mem2) ->
  SRr rsegs W cfg (w6cb_hpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs pc clob Wr Q2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs pc clob Wr cfg Q1 Q2 H HQ.
eapply SRr_mono; [exact H|].
intros W2 c2 _ (regs2 & mem2 & md2 & E1 & E2 & HJ2 & Hio & Hr & Hm & HQ1).
exists regs2, mem2, md2. repeat (split; [assumption|]). exact (HQ _ _ HQ1).
Qed.

(* the geometry of the real frame R, the frame for locals F and the table t8 *)
Lemma w8_geo_ok : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  w6cb_geo STK sp0 own lyc R F pos ->
  (forall o, 0 <= o < 1024 -> apresent (w_H W) memc (F + o)) /\
  0x10007fff8000 + 16384 <= R /\ R + 0x200 <= 2 ^ 47 /\ 4096 <= F /\ F + 1024 <= R - 16384 /\
  (F + 0x218 <= 0x7fff8000 \/ 0x7fff8000 + 2 ^ 44 <= F) /\
  (forall a, W6CB_T8 <= a < W6CB_T8 + 16 -> ~ (F <= a < F + 1024)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ (HR16 & HRs & HRsp & HRhi & Hown & HF & HFapp & HF32).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & HFp & _).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite <- HF in HFp, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFp, HFceil.
unfold T_SEG_STK, ASTACK in HRs, HRhi.
split; [intros o Ho; exact (proj1 (HFp (F + o) ltac:(lia)))|].
split; [unfold kHighMemBeg in HRhi; lia|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp; lia|].
intros a Ha Hf.
assert (Hfa : frame_addr lyc 4 pos <= a < frame_addr lyc 4 pos + fs_frame_bytes 4)
  by (rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia).
apply (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR
  (or_intror (or_introl (ex_intro _ 4 (ex_intro _ pos (conj Hin4 Hfa))))))).
exact (w8_tbl_img a Ha).
Qed.

(* ---- no byte left: 0x8122c `beqz s6` -> 0x8155c .. 0x81580 (e62.type := 4, e62.size := 0) ---- *)
Lemma w8_p0 : forall hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c pp : Z),
  w6cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6cb_regs B regs R c (Z.of_nat (length ([] : list byte))) -> w6cb_cells W memc R F pp -> w6cb_in W memc R F c [] ->
  w8_Flo hi <= F <= w8_Fhi hi ->
  SRr rsegs W (cfg_at rsegs W6CB_D8 regs memc mdc)
    (w6cb_hpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6CB_SET w6cb_clob8 (w6cb_hdr_wr F)
      (w8_Q W F 4 0 0 c)).
Proof.
intros hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp
  (HJ & (HR16 & HRs & HRsp & HRhi & Hown & HF & HFapp & HF32) & Hrom)
  (H2 & H3 & H4 & H9 & H27 & H18 & H22 & H16 & H6 & H20) (V158 & V110 & V10 & V130 & Hpp0 & Hpp1)
  (Hbytes & Hrain & Hhull & Hc1 & Hc63 & Hamr & Hdis) HFhi.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsl.
destruct (w8_geo_ok STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ
  (conj HR16 (conj HRs (conj HRsp (conj HRhi (conj Hown (conj HF (conj HFapp HF32))))))))
  as (HFp & HRk & HRtop & HF4096 & HFR & HFsh & HTF).
unfold T_SEG_STK, ASTACK in HRs, HRhi, Hdis.
set (n := Z.of_nat (length ([] : list byte))) in *.
assert (Hn : n = 0) by reflexivity.
pose (t := 0). pose (s := 0).
assert (Ht : t = 0) by reflexivity. assert (Hs : s = 0) by reflexivity. assert (Htm : t mod 4 = 0) by reflexivity.
assert (Hcn : c + n <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
destruct (w8_ef regs F t s R c n H9 H16 H6 H27) as (E9 & E16 & E6 & E27 & E32 & E33 & E34 & E35 & E36 & E37).
assert (HS0 : st_ok rsegs (Ereg regs (w8_extra F t s)) (mkSS W6CB_D8 sr_atoms (w8_regs false) None (w8_G hi (2 ^ 47 - 2) 0 0 0 2))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6CB_D8) memc (seg_rom rsegs)))).
{ apply (w8_entry W regs memc R F c t s false _ H9 H16); try lia.
  - exact V110.
  - exact V158.
  - intros o Ho. exact (HFp o ltac:(lia)).
  - apply (w8_G_ok regs F t s R c n hi (2 ^ 47 - 2) 0 0 0 2 H27 H9 H16 H22 H6); lia. }
pose proof (st_ok_pin_sv rsegs _ _ _ (18%bv : bv 5) (SOff 16 1) HS0 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H18; apply (w8_den_off _ _ _ (c - 1)); [exact E16 | lia | lia | lia])) as HS1.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 1 HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H20; reflexivity)) as HS.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs w8_Bx [] (Ereg regs (w8_extra F t s)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (w8_extra F t s)) (Ereg regs (w8_extra F t s))) by apply env_agree_refl.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 W6CB_D8) with (Z_to_bv 64 W6CB_D8).
pose proof (st_ok_pin_lit rsegs _ _ _ (22%bv : bv 5) 0 HS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H22; reflexivity)) as HS1.
clear HS. rename HS1 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
destruct hi;
( aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w8_Bspan W6CB_SET; [w8_awr E32 pos Hown HF | idtac];
  w8_keep E32;
  w8_leaf F HAE [(20%bv : bv 5, SLit 1)]
    ltac:(intros ? ? [Hp|[]]; injection Hp as <- <-; cbn [sv_denot]; rewrite H20; reflexivity)
    ltac:(reflexivity)
    ltac:(apply (w8_den_off _ _ _ (c - 1)); [w8_ew E16 | lia | lia | lia])
    ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity) E32 ).
Qed.

(* ---- a byte t with t & 3 = 3 (a String): the type t8[3], no second byte read, size 0 (0x81330) ---- *)
Lemma w8_p1s : forall hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos c pp : Z) (b : byte) (r1 : list byte),
  w6cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6cb_regs B regs R c (Z.of_nat (length (b :: r1))) -> w6cb_cells W memc R F pp -> w6cb_in W memc R F c (b :: r1) ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6CB_T8 16 ->
  w8_Flo hi <= F <= w8_Fhi hi -> bv_unsigned b mod 4 = 3 ->
  SRr rsegs W (cfg_at rsegs W6CB_D8 regs memc mdc)
    (w6cb_hpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6CB_SET w6cb_clob8 (w6cb_hdr_wr F)
      (w8_Q W F (w6cb_ty8 (bv_unsigned b)) 0 (Z.of_nat (length r1)) (c + 1))).
Proof.
intros hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b r1
  (HJ & (HR16 & HRs & HRsp & HRhi & Hown & HF & HFapp & HF32) & Hrom)
  (H2 & H3 & H4 & H9 & H27 & H18 & H22 & H16 & H6 & H20) (V158 & V110 & V10 & V130 & Hpp0 & Hpp1)
  (Hbytes & Hrain & Hhull & Hc1 & Hc63 & Hamr & Hdis) Hra8 HFhi Hs3.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsl.
destruct (w8_geo_ok STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ
  (conj HR16 (conj HRs (conj HRsp (conj HRhi (conj Hown (conj HF (conj HFapp HF32))))))))
  as (HFp & HRk & HRtop & HF4096 & HFR & HFsh & HTF).
unfold T_SEG_STK, ASTACK in HRs, HRhi, Hdis.
pose proof (HTF W6CB_T8 ltac:(unfold W6CB_T8; lia)) as HT0.
pose proof (HTF (W6CB_T8 + 15) ltac:(unfold W6CB_T8; lia)) as HT15.
set (n := Z.of_nat (length (b :: r1))) in *.
assert (Hn : n = Z.of_nat (length r1) + 1) by (subst n; cbn [length]; lia).
pose proof (Cursor.byte_range b) as Hb.
set (t := bv_unsigned b) in *. pose (s := 0). assert (Hs : s = 0) by reflexivity.
pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as Htm.
pose proof (w8_ty8_in t) as Hty. assert (Htyr : 2 <= w6cb_ty8 t <= 8) by (cbn [In] in Hty; lia).
assert (Hcn : c + n <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (V1 : val_mem rsegs (mrestrict (w_H W) memc) (c - 1 + 1) 1 t).
{ replace (c - 1 + 1) with (c + Z.of_nat 0) by lia. exact (rm_bytes_byte rsegs _ _ _ _ 0%nat Hbytes ltac:(cbn; lia)). }
assert (D0 := Hdis c ltac:(lia)).
destruct (w8_ef regs F t s R c n H9 H16 H6 H27) as (E9 & E16 & E6 & E27 & E32 & E33 & E34 & E35 & E36 & E37).
assert (HS0 : st_ok rsegs (Ereg regs (w8_extra F t s)) (mkSS W6CB_D8 sr_atoms (w8_regs true) None
    (w8_G hi (2 ^ 47 - 3) 1 (2 ^ 47 - 2) 3 3)) (restrict (w_H W) (mkst regs (Z_to_bv 64 W6CB_D8) memc (seg_rom rsegs)))).
{ apply (w8_entry W regs memc R F c t s true _ H9 H16); try lia.
  - exact V110.
  - exact V158.
  - intros o Ho. exact (HFp o ltac:(lia)).
  - intros _. split; [exact V1|]. split; [lia|]. lia.
  - apply (w8_G_ok regs F t s R c n hi (2 ^ 47 - 3) 1 (2 ^ 47 - 2) 3 3 H27 H9 H16 H22 H6); lia. }
pose proof (st_ok_pin_sv rsegs _ _ _ (18%bv : bv 5) (SOff 16 1) HS0 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H18; apply (w8_den_off _ _ _ (c - 1)); [exact E16 | lia | lia | lia])) as HS1.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 1 HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H20; reflexivity)) as HS.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs w8_Bx [] (Ereg regs (w8_extra F t s)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (w8_extra F t s)) (Ereg regs (w8_extra F t s))) by apply env_agree_refl.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 W6CB_D8) with (Z_to_bv 64 W6CB_D8).
destruct hi;
( (* 0x8122c .. 0x81284: the trap test, the checks of t and of t8[t & 3], the trap test; then a0 := the entry's
     atom, a1 := 3 *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w8_Bspan W8_U;
  [ w8_obl_tbl E27 E33 Hra8 t | w8_obl_cur E27 E16 Hrain (c - 1) | w8_awr E32 pos Hown HF | idtac ];
  w8_keep E32;
  w8_pin (10%bv : bv 5) (SOff 35 0) (W6CB_T8 + 4 * (t mod 4))
    ltac:(apply (w8_den_off _ _ _ (W6CB_T8 + 4 * (t mod 4))); [w8_ew E35 | unfold W6CB_T8; lia | unfold W6CB_T8; lia | lia])
    ltac:(apply (w8_chk _ 33 (map Z.of_nat (seq 0 256)) (fun v => W6CB_T8 + 4 * (v mod 4)));
          [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E33 | apply w8_in256; lia]);
  w8_pin (11%bv : bv 5) (SLit 3) 3 ltac:(reflexivity)
    ltac:(transitivity (Z_to_bv 64 (t mod 4));
          [ apply (w8_chk _ 33 (map Z.of_nat (seq 0 256)) (fun v => v mod 4));
            [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E33 | apply w8_in256; lia]
          | rewrite Hs3; reflexivity ]);
  (* the input byte out, the table entry in *)
  w8_drop 3%nat;
  w8_add w8_RT
    ltac:(apply (w8_RT_ok _ W _ memc F t); [w8_ew E35 | w8_ew E36 | lia | exact Hrom | exact KE | exact HTF])
    ltac:(cbn [ss_mem];
          repeat (apply Forall_cons;
            [unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val w8_RT]; w8_strip;
             rewrite ?E9, ?E32, ?E35; rewrite ?unsigned_lit_small by (unfold W6CB_T8; lia); unfold W6CB_T8 in *; lia |]);
          apply Forall_nil);
  (* 0x81284 .. 0x51608: the `lw`, e62.type, `beq a1,a0` taken, size 0, the call *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w8_Bspan W6CB_SET; [w8_awr E32 pos Hown HF | idtac];
  w8_keep E32;
  w8_leaf F HAE [(20%bv : bv 5, SLit 1)]
    ltac:(intros ? ? [Hp|[]]; injection Hp as <- <-; cbn [sv_denot]; rewrite H20; reflexivity)
    ltac:(reflexivity)
    ltac:(apply (w8_den_off _ _ _ (c - 1)); [w8_ew E16 | lia | lia | lia])
    ltac:(apply (w8_den_off _ _ _ (n + 1)); [w8_ew E6 | lia | lia | lia])
    ltac:(apply (w8_chk _ 36 [4; 6; 2; 8] (fun v => v)); [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E36 | exact Hty])
    ltac:(reflexivity) E32 ).
Qed.

(* ---- one byte t, t & 3 <> 3, nothing after it: s6 = 0 sends the head to 0x81330, size 0 ---- *)
Lemma w8_p1n : forall hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos c pp : Z) (b : byte),
  w6cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6cb_regs B regs R c (Z.of_nat (length [b])) -> w6cb_cells W memc R F pp -> w6cb_in W memc R F c [b] ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6CB_T8 16 ->
  w8_Flo hi <= F <= w8_Fhi hi -> bv_unsigned b mod 4 <> 3 ->
  SRr rsegs W (cfg_at rsegs W6CB_D8 regs memc mdc)
    (w6cb_hpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6CB_SET w6cb_clob8 (w6cb_hdr_wr F)
      (w8_Q W F (w6cb_ty8 (bv_unsigned b)) 0 0 (c + 1))).
Proof.
intros hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b
  (HJ & (HR16 & HRs & HRsp & HRhi & Hown & HF & HFapp & HF32) & Hrom)
  (H2 & H3 & H4 & H9 & H27 & H18 & H22 & H16 & H6 & H20) (V158 & V110 & V10 & V130 & Hpp0 & Hpp1)
  (Hbytes & Hrain & Hhull & Hc1 & Hc63 & Hamr & Hdis) Hra8 HFhi Hnot3.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsl.
destruct (w8_geo_ok STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ
  (conj HR16 (conj HRs (conj HRsp (conj HRhi (conj Hown (conj HF (conj HFapp HF32))))))))
  as (HFp & HRk & HRtop & HF4096 & HFR & HFsh & HTF).
unfold T_SEG_STK, ASTACK in HRs, HRhi, Hdis.
pose proof (HTF W6CB_T8 ltac:(unfold W6CB_T8; lia)) as HT0.
pose proof (HTF (W6CB_T8 + 15) ltac:(unfold W6CB_T8; lia)) as HT15.
set (n := Z.of_nat (length [b])) in *.
assert (Hn : n = 1) by reflexivity.
pose proof (Cursor.byte_range b) as Hb.
set (t := bv_unsigned b) in *. pose (s := 0). assert (Hs : s = 0) by reflexivity.
pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as Htm.
pose proof (w8_ty8_in t) as Hty. assert (Htyr : 2 <= w6cb_ty8 t <= 8) by (cbn [In] in Hty; lia).
assert (Hcn : c + n <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (V1 : val_mem rsegs (mrestrict (w_H W) memc) (c - 1 + 1) 1 t).
{ replace (c - 1 + 1) with (c + Z.of_nat 0) by lia. exact (rm_bytes_byte rsegs _ _ _ _ 0%nat Hbytes ltac:(cbn; lia)). }
assert (D0 := Hdis c ltac:(lia)).
destruct (w8_ef regs F t s R c n H9 H16 H6 H27) as (E9 & E16 & E6 & E27 & E32 & E33 & E34 & E35 & E36 & E37).
assert (HS0 : st_ok rsegs (Ereg regs (w8_extra F t s)) (mkSS W6CB_D8 sr_atoms (w8_regs true) None
    (w8_G hi (2 ^ 47 - 3) 1 1 0 2)) (restrict (w_H W) (mkst regs (Z_to_bv 64 W6CB_D8) memc (seg_rom rsegs)))).
{ apply (w8_entry W regs memc R F c t s true _ H9 H16); try lia.
  - exact V110.
  - exact V158.
  - intros o Ho. exact (HFp o ltac:(lia)).
  - intros _. split; [exact V1|]. split; [lia|]. lia.
  - apply (w8_G_ok regs F t s R c n hi (2 ^ 47 - 3) 1 1 0 2 H27 H9 H16 H22 H6); lia. }
pose proof (st_ok_pin_sv rsegs _ _ _ (18%bv : bv 5) (SOff 16 1) HS0 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H18; apply (w8_den_off _ _ _ (c - 1)); [exact E16 | lia | lia | lia])) as HS1.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 1 HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H20; reflexivity)) as HS.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs w8_Bx [] (Ereg regs (w8_extra F t s)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (w8_extra F t s)) (Ereg regs (w8_extra F t s))) by apply env_agree_refl.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 W6CB_D8) with (Z_to_bv 64 W6CB_D8).
(* t1 = 2: the engine computes s6 = t1 - 2 = 0 and takes `beqz s6` *)
pose proof (st_ok_pin_lit rsegs _ _ _ (6%bv : bv 5) 2 HS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H6; reflexivity)) as HS1.
clear HS. rename HS1 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
destruct hi;
( (* 0x8122c .. 0x81284: the trap test, the checks of t and of t8[t & 3], the trap test; then a0 := the entry's
     atom, a1 := t mod 4's *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w8_Bspan W8_U;
  [ w8_obl_tbl E27 E33 Hra8 t | w8_obl_cur E27 E16 Hrain (c - 1) | w8_awr E32 pos Hown HF | idtac ];
  w8_keep E32;
  w8_pin (10%bv : bv 5) (SOff 35 0) (W6CB_T8 + 4 * (t mod 4))
    ltac:(apply (w8_den_off _ _ _ (W6CB_T8 + 4 * (t mod 4))); [w8_ew E35 | unfold W6CB_T8; lia | unfold W6CB_T8; lia | lia])
    ltac:(apply (w8_chk _ 33 (map Z.of_nat (seq 0 256)) (fun v => W6CB_T8 + 4 * (v mod 4)));
          [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E33 | apply w8_in256; lia]);
  w8_pin (11%bv : bv 5) (SOff 37 0) (t mod 4)
    ltac:(apply (w8_den_off _ _ _ (t mod 4)); [w8_ew E37 | lia | lia | lia])
    ltac:(apply (w8_chk _ 33 (map Z.of_nat (seq 0 256)) (fun v => v mod 4));
          [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E33 | apply w8_in256; lia]);
  (* the input byte out, the table entry in *)
  w8_drop 3%nat;
  w8_add w8_RT
    ltac:(apply (w8_RT_ok _ W _ memc F t); [w8_ew E35 | w8_ew E36 | lia | exact Hrom | exact KE | exact HTF])
    ltac:(cbn [ss_mem];
          repeat (apply Forall_cons;
            [unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val w8_RT]; w8_strip;
             rewrite ?E9, ?E32, ?E35; rewrite ?unsigned_lit_small by (unfold W6CB_T8; lia); unfold W6CB_T8 in *; lia |]);
          apply Forall_nil);
  (* 0x81284 .. 0x51608: the `lw`, e62.type, `beq a1,a0` not taken, `beqz s6` taken, size 0, the call *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w8_Bspan W6CB_SET; [w8_awr E32 pos Hown HF | idtac];
  w8_keep E32;
  w8_leaf F HAE [(20%bv : bv 5, SLit 1); (6%bv : bv 5, SLit 2)]
    ltac:(intros ? ? [Hp|[Hp|[]]]; injection Hp as <- <-; cbn [sv_denot];
          first [rewrite H20; reflexivity | rewrite H6; reflexivity])
    ltac:(reflexivity)
    ltac:(apply (w8_den_off _ _ _ (c - 1)); [w8_ew E16 | lia | lia | lia])
    ltac:(first [reflexivity | apply (w8_den_off _ _ _ (n + 1)); [w8_ew E6 | lia | lia | lia]])
    ltac:(apply (w8_chk _ 36 [4; 6; 2; 8] (fun v => v)); [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E36 | exact Hty])
    ltac:(reflexivity) E32 ).
Qed.

(* ---- two bytes t, s with t & 3 <> 3: the trap test and the second check (0x812a4 .. 0x812bc), size s & 3 ---- *)
Lemma w8_p2 : forall hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos c pp : Z) (b b2 : byte) (r2 : list byte),
  w6cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6cb_regs B regs R c (Z.of_nat (length (b :: b2 :: r2))) -> w6cb_cells W memc R F pp ->
  w6cb_in W memc R F c (b :: b2 :: r2) ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6CB_T8 16 ->
  w8_Flo hi <= F <= w8_Fhi hi -> bv_unsigned b mod 4 <> 3 ->
  SRr rsegs W (cfg_at rsegs W6CB_D8 regs memc mdc)
    (w6cb_hpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6CB_SET w6cb_clob8 (w6cb_hdr_wr F)
      (w8_Q W F (w6cb_ty8 (bv_unsigned b)) (bv_unsigned b2 mod 4) (Z.of_nat (length r2)) (c + 2))).
Proof.
intros hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b b2 r2
  (HJ & (HR16 & HRs & HRsp & HRhi & Hown & HF & HFapp & HF32) & Hrom)
  (H2 & H3 & H4 & H9 & H27 & H18 & H22 & H16 & H6 & H20) (V158 & V110 & V10 & V130 & Hpp0 & Hpp1)
  (Hbytes & Hrain & Hhull & Hc1 & Hc63 & Hamr & Hdis) Hra8 HFhi Hnot3.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsl.
destruct (w8_geo_ok STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ
  (conj HR16 (conj HRs (conj HRsp (conj HRhi (conj Hown (conj HF (conj HFapp HF32))))))))
  as (HFp & HRk & HRtop & HF4096 & HFR & HFsh & HTF).
unfold T_SEG_STK, ASTACK in HRs, HRhi, Hdis.
pose proof (HTF W6CB_T8 ltac:(unfold W6CB_T8; lia)) as HT0.
pose proof (HTF (W6CB_T8 + 15) ltac:(unfold W6CB_T8; lia)) as HT15.
set (n := Z.of_nat (length (b :: b2 :: r2))) in *.
assert (Hn : n = Z.of_nat (length r2) + 2) by (subst n; cbn [length]; lia).
pose proof (Cursor.byte_range b) as Hb. pose proof (Cursor.byte_range b2) as Hb2.
set (t := bv_unsigned b) in *. set (s := bv_unsigned b2) in *.
pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as Htm.
pose proof (Z.mod_pos_bound s 4 ltac:(lia)) as Hsm.
pose proof (w8_ty8_in t) as Hty. assert (Htyr : 2 <= w6cb_ty8 t <= 8) by (cbn [In] in Hty; lia).
assert (Hcn : c + n <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (V1 : val_mem rsegs (mrestrict (w_H W) memc) (c - 1 + 1) 1 t).
{ replace (c - 1 + 1) with (c + Z.of_nat 0) by lia. exact (rm_bytes_byte rsegs _ _ _ _ 0%nat Hbytes ltac:(cbn; lia)). }
assert (V2 : val_mem rsegs (mrestrict (w_H W) memc) (c - 1 + 2) 1 s).
{ replace (c - 1 + 2) with (c + Z.of_nat 1) by lia. exact (rm_bytes_byte rsegs _ _ _ _ 1%nat Hbytes ltac:(cbn; lia)). }
assert (D0 := Hdis c ltac:(lia)).
assert (D1 := Hdis (c + 1) ltac:(lia)).
destruct (w8_ef regs F t s R c n H9 H16 H6 H27) as (E9 & E16 & E6 & E27 & E32 & E33 & E34 & E35 & E36 & E37).
assert (HS0 : st_ok rsegs (Ereg regs (w8_extra F t s)) (mkSS W6CB_D8 sr_atoms (w8_regs true) None
    (w8_G hi (2 ^ 47 - 4) 2 (2 ^ 47 - 2) 0 2)) (restrict (w_H W) (mkst regs (Z_to_bv 64 W6CB_D8) memc (seg_rom rsegs)))).
{ apply (w8_entry W regs memc R F c t s true _ H9 H16); try lia.
  - exact V110.
  - exact V158.
  - intros o Ho. exact (HFp o ltac:(lia)).
  - intros _. split; [exact V1|]. split; [lia|]. lia.
  - apply (w8_G_ok regs F t s R c n hi (2 ^ 47 - 4) 2 (2 ^ 47 - 2) 0 2 H27 H9 H16 H22 H6); lia. }
pose proof (st_ok_pin_sv rsegs _ _ _ (18%bv : bv 5) (SOff 16 1) HS0 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H18; apply (w8_den_off _ _ _ (c - 1)); [exact E16 | lia | lia | lia])) as HS1.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 1 HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite H20; reflexivity)) as HS.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs w8_Bx [] (Ereg regs (w8_extra F t s)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (w8_extra F t s)) (Ereg regs (w8_extra F t s))) by apply env_agree_refl.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 W6CB_D8) with (Z_to_bv 64 W6CB_D8).
destruct hi;
( (* 0x8122c .. 0x81284: the trap test, the checks of t and of t8[t & 3], the trap test; then a0 := the entry's
     atom, a1 := t mod 4's *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w8_Bspan W8_U;
  [ w8_obl_tbl E27 E33 Hra8 t | w8_obl_cur E27 E16 Hrain (c - 1) | w8_awr E32 pos Hown HF | idtac ];
  w8_keep E32;
  w8_pin (10%bv : bv 5) (SOff 35 0) (W6CB_T8 + 4 * (t mod 4))
    ltac:(apply (w8_den_off _ _ _ (W6CB_T8 + 4 * (t mod 4))); [w8_ew E35 | unfold W6CB_T8; lia | unfold W6CB_T8; lia | lia])
    ltac:(apply (w8_chk _ 33 (map Z.of_nat (seq 0 256)) (fun v => W6CB_T8 + 4 * (v mod 4)));
          [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E33 | apply w8_in256; lia]);
  w8_pin (11%bv : bv 5) (SOff 37 0) (t mod 4)
    ltac:(apply (w8_den_off _ _ _ (t mod 4)); [w8_ew E37 | lia | lia | lia])
    ltac:(apply (w8_chk _ 33 (map Z.of_nat (seq 0 256)) (fun v => v mod 4));
          [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E33 | apply w8_in256; lia]);
  (* the input byte out, the table entry in *)
  w8_drop 3%nat;
  w8_add w8_RT
    ltac:(apply (w8_RT_ok _ W _ memc F t); [w8_ew E35 | w8_ew E36 | lia | exact Hrom | exact KE | exact HTF])
    ltac:(cbn [ss_mem];
          repeat (apply Forall_cons;
            [unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val w8_RT]; w8_strip;
             rewrite ?E9, ?E32, ?E35; rewrite ?unsigned_lit_small by (unfold W6CB_T8; lia); unfold W6CB_T8 in *; lia |]);
          apply Forall_nil);
  (* 0x81284 .. 0x812a4: the `lw`, e62.type; t & 3 <> 3 and s6 = |r| - 1 > 0 fall through *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w8_Bspan W8_V; [w8_awr E32 pos Hown HF | idtac];
  w8_keep E32;
  (* the table entry out, the second input byte in *)
  w8_drop 0%nat;
  w8_add w8_RS
    ltac:(apply (w8_RS_ok _ W _ memc F c s); [w8_ew E16 | w8_ew E34 | lia | lia | lia | exact V2 | exact KE
          | unfold w6cb_hdr_wr; lia])
    ltac:(cbn [ss_mem];
          repeat (apply Forall_cons;
            [unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val w8_RS]; w8_strip;
             rewrite ?E9, ?E32, ?E16; rewrite ?unsigned_lit_small by lia; lia |]);
          apply Forall_nil);
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?ms) |- _ =>
    assert (Hra2 : range_addressable (aview rsegs (w_H W) (ms_mem ms)) SHADOW_OFF (c + 1) 1)
      by (apply (w8_ra_kept _ memc); [apply (ra_sub _ _ c n); [exact Hrain | lia | lia] |];
          intros x Hx; unfold shadow_of_addr;
          assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
          apply KE; [unfold SHADOW_OFF; lia | unfold w6cb_hdr_wr, SHADOW_OFF; lia])
  end;
  (* 0x812a4 .. 0x51608: the trap test, the check of the second byte, e62.size, the call *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK w8_Bspan W6CB_SET;
  [w8_obl_cur E27 E16 Hra2 (c - 1) | w8_awr E32 pos Hown HF | idtac];
  w8_keep E32;
  w8_leaf F HAE [(20%bv : bv 5, SLit 1)]
    ltac:(intros ? ? [Hp|[]]; injection Hp as <- <-; cbn [sv_denot]; rewrite H20; reflexivity)
    ltac:(apply (w8_chk _ 34 (map Z.of_nat (seq 0 256)) (fun v => v mod 4));
          [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E34 | apply w8_in256; lia])
    ltac:(apply (w8_den_off _ _ _ (c - 1)); [w8_ew E16 | lia | lia | lia])
    ltac:(apply (w8_den_off _ _ _ (n + 1)); [w8_ew E6 | lia | lia | lia])
    ltac:(apply (w8_chk _ 36 [4; 6; 2; 8] (fun v => v)); [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E36 | exact Hty])
    ltac:(apply (w8_chk _ 34 (map Z.of_nat (seq 0 256)) (fun v => v mod 4));
          [vm_compute; reflexivity | vm_compute; reflexivity | w8_ew E34 | apply w8_in256; lia]) E32 ).
Qed.

End d.

(* ======================================== the block lemma ======================================== *)
Theorem w6cb_h8 : forall B, w6cb_h8_stmt B.
Proof.
intros B. unfold w6cb_h8_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp r Hctx Hregs Hcells Hin He0 Hra8.
pose proof Hctx as (_ & (_ & _ & _ & _ & _ & _ & HFapp & _) & _).
destruct (w8_hi_of F HFapp) as (hi & Hhi).
destruct r as [|b r1].
- (* no byte left *)
  eapply w8_hpost_mono; [exact (w8_p0 B hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp
    Hctx Hregs Hcells Hin Hhi)|].
  intros regs2 mem2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). cbv beta zeta.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  split; [rewrite A5; unfold w64; f_equal;
          lazymatch goal with |- _ = _ + ?a - ?b =>
            let a' := eval vm_compute in a in let b' := eval vm_compute in b in change a with a'; change b with b' end;
          lia|].
  split; [exact A6|]. split; [exact A7 | exact A8].
- destruct (Z.eq_dec (bv_unsigned b mod 4) 3) as [Hs3|Hs3].
  + (* t & 3 = 3: a String *)
    eapply w8_hpost_mono; [exact (w8_p1s B hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp
      b r1 Hctx Hregs Hcells Hin Hra8 Hhi Hs3)|].
    intros regs2 mem2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). cbv beta zeta. cbn [Cursor.fuzz_u8 fst snd].
    unfold w6cb_sz8. rewrite w8_ty8_str, Hs3. cbn [Z.eqb Pos.eqb fst snd].
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
    split; [rewrite A5; unfold w64; f_equal; cbn [length]; lia|].
    split; [exact A6|]. split; [exact A7 | exact A8].
  + destruct r1 as [|b2 r2].
    * (* one byte, not a String: s6 = 0 *)
      eapply w8_hpost_mono; [exact (w8_p1n B hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp
        b Hctx Hregs Hcells Hin Hra8 Hhi Hs3)|].
      intros regs2 mem2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). cbv beta zeta. cbn [Cursor.fuzz_u8 fst snd].
      unfold w6cb_sz8. rewrite w8_ty8_str, (proj2 (Z.eqb_neq _ _) Hs3). cbn [fst snd Cursor.fuzz_u8].
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
      split; [rewrite A5; unfold w64; f_equal; cbn [length]; lia|].
      split; [exact A6|]. split; [exact A7 | exact A8].
    * (* two bytes, not a String: the size s & 3 *)
      eapply w8_hpost_mono; [exact (w8_p2 B hi STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp
        b b2 r2 Hctx Hregs Hcells Hin Hra8 Hhi Hs3)|].
      intros regs2 mem2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). cbv beta zeta. cbn [Cursor.fuzz_u8 fst snd].
      unfold w6cb_sz8. rewrite w8_ty8_str, (proj2 (Z.eqb_neq _ _) Hs3). cbn [fst snd Cursor.fuzz_u8].
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
      split; [rewrite A5; unfold w64; f_equal; cbn [length]; lia|].
      split; [exact A6|]. split; [exact A7 | exact A8].
Qed.

End b.
