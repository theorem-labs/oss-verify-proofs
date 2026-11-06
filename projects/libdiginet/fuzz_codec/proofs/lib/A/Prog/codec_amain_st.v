(* The executor states of the image-A walk of LLVMFuzzerTestOneInput (fuzz_codec.asan, entry 0x8084c) at its cuts:
   the bridge from a cut of lib/A/Prog/codec_amain_inv.v (the journal at [(3, pos)], mcommon and the cut's own
   facts) to the executor's st_ok state a segment walk starts from.

   The environment. At a cut with the registers regs2, the input cursor at c bytes taken and the segment's own extra
   atoms ys, the walk runs in E = am_env g pos c regs2 ys = Ereg regs2 (cw_extra (am_xs g pos c ++ ys)):
     atoms 0 .. 31   the registers regs2 (so 2 = 9 = sp1, 8 = sp0, 26 = ops, ...)
     atom 32         SB, the shadow offset (CPgWalk's CW_Bx)
     atom 33         F = frame_addr (e_ly g) 3 pos, the entry's side-stack frame (64-aligned)
     atom 34         shadow_addr F
     atom 35         e_p g + c, the cursor in.p
     atom 36         e_n g - c, the bytes left in.n
     atoms 37 ..     the segment's ys (AM_X0 + j holds nth j ys)
   The registers of the state (am_sregs): every register is its own atom, except that s1 = sp is atom 2, s2 is
   atom 34, s3 / s6 / s9 are F + 432 / F + 176 / F + 64 (offsets of atom 33), s4 is atom 32 (so an instrumented
   check `(x >> 3) + s4` matches the token layer's Bx), s5 is the literal -8 and s11 the literal 10.
   The atom facts (am_atoms): 2 in [2^46, 2^47] 32-aligned; 32 = SB; 33 in [4096, AM_HI] 64-aligned;
   34 in [SB + 512, SB + 2^44] 8-aligned; 35 in [4096, AM_HI]; 36 in [0, 2^26 - 1].
   The base regions (am_regs): CPgWalk's cw_regs 0 (an empty save area, the .got slot of the shadow-offset cell
   and the cell), the spills 16(sp1) .. 120(sp1) as read-only 8-byte chunks (am_spill_region), and the cursor
   152(sp1) / 160(sp1) as a writable window with the chunks atom 35 / atom 36 (am_cur_region). am_regs0 is the
   base without the cursor (for EXIT, whose cut carries no cursor).
   A segment adds its own regions rs and atom facts AF: am_ss pc rs AF. It proves region_ok of rs, their pairwise
   disjointness and each one's disjointness from am_regs (the am_apart_* lemmas give the last one from where the
   region lies), and atoms_ok of AF. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkImg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ the atoms, registers, regions and facts ================================ *)
Definition AM_F : nat := 33.
Definition AM_SH : nat := 34.
Definition AM_CP : nat := 35.
Definition AM_CN : nat := 36.
Definition AM_X0 : nat := 37.
(* the top of the allocator's range (asan_consts: alloc_ceiling <= AM_HI) *)
Definition AM_HI : Z := 0x7fffff800000.

Definition am_sregs : list sv :=
[SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 8 0; SOff 2 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 34 0; SOff 33 432; SOff 32 0; SLit 18446744073709551608; SOff 33 176; SOff 23 0;
 SOff 24 0; SOff 33 64; SOff 26 0; SLit 10; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].

(* the spills, 0x80a20-0x80ab8 (mcommon), as offsets of the frame atom 33 *)
Definition am_spill_chunks : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SOff 33 223)); YP09.mkChunk 24 (CVal 8 (SOff 33 34));
 YP09.mkChunk 32 (CVal 8 (SOff 33 32)); YP09.mkChunk 40 (CVal 8 (SOff 33 320));
 YP09.mkChunk 48 (CVal 8 (SLit 0x5cb0)); YP09.mkChunk 56 (CVal 8 (SOff 33 324));
 YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 8 (SOff 33 0));
 YP09.mkChunk 80 (CVal 8 (SLit 0x13f0)); YP09.mkChunk 88 (CVal 8 (SOff 33 216));
 YP09.mkChunk 96 (CVal 8 (SOff 33 284)); YP09.mkChunk 104 (CVal 8 (SOff 33 344));
 YP09.mkChunk 112 (CVal 8 (SLit 0x20f40)); YP09.mkChunk 120 (CVal 8 (SOff 33 252))].
Definition am_spill_region : YP09.region := YP09.mkRegion (Some 2%nat) 16 128 0 0 am_spill_chunks.
(* struct fuzz_in at 152(sp1): in.p, in.n *)
Definition am_cur_region : YP09.region :=
YP09.mkRegion (Some 2%nat) 152 168 152 168 [YP09.mkChunk 152 (CVal 8 (SOff 35 0)); YP09.mkChunk 160 (CVal 8 (SOff 36 0))].
Definition am_regs0 : smem := cw_regs 0 ++ [am_spill_region].
Definition am_regs : smem := am_regs0 ++ [am_cur_region].

Definition am_atoms : list (nat * afact) :=
[(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 AM_HI 6);
 (34%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3); (35%nat, mkAF 4096 AM_HI 0); (36%nat, mkAF 0 (2 ^ 26 - 1) 0)].

(* the state at a cut: the base, then the segment's own regions and atom facts *)
Definition am_ssb (base : smem) (pc : Z) (rs : smem) (AF : list (nat * afact)) : sstate :=
mkSS pc am_sregs (base ++ rs) None (mkFacts (am_atoms ++ AF) [] []).
Definition am_ss (pc : Z) (rs : smem) (AF : list (nat * afact)) : sstate := am_ssb am_regs pc rs AF.
Definition am_ss0 (pc : Z) (rs : smem) (AF : list (nat * afact)) : sstate := am_ssb am_regs0 pc rs AF.

(* ---- the builders' region shapes ----
   am_frame_region: a range [lo, hi) of the frame (atom 33) with the chunks the segment gives: the call record
   k = F + 176 (184 bytes), text = F + 64 (65), SCRIBBLE's payload F + 32 (10), the dots byte F + 432.
   am_shadow_region: the frame's 56 shadow bytes (atom 34), one 1-byte chunk each, writable in [wlo, whi). *)
Definition am_frame_region (lo hi wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 33%nat) lo hi wlo whi cs.
Fixpoint am_sh_chunks (vs : list Z) (i : Z) : list YP09.chunk :=
match vs with [] => [] | v :: vs' => YP09.mkChunk i (CVal 1 (SLit v)) :: am_sh_chunks vs' (i + 1) end.
Definition am_shadow_region (wlo whi : Z) (vs : list Z) : YP09.region :=
YP09.mkRegion (Some 34%nat) 0 56 wlo whi (am_sh_chunks vs 0).
(* the two shadow maps of the frame, as the engine wants them (literal lists) *)
Definition am_shm0 : list Z := Eval vm_compute in shm 0.
Definition am_shm8 : list Z := Eval vm_compute in shm SH_F8.
Lemma am_shm0_eq : am_shm0 = shm 0. Proof. vm_compute. reflexivity. Qed.
Lemma am_shm8_eq : am_shm8 = shm SH_F8. Proof. vm_compute. reflexivity. Qed.

(* the registers every cut after the prologue fixes *)
Definition AM_KEEPR : list (bv 5) := [2; 9; 8; 3; 4; 20; 18; 21; 22; 25; 19; 27]%bv.
Definition am_keep_ok (sr : list sv) : bool :=
forallb (fun r => sv_eqb (sr_get sr r) (sr_get am_sregs r)) AM_KEEPR.
(* the read-only test of an image range, by computation over the loaded segments *)
Definition am_ro_b (q n : Z) : bool :=
existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? q) &&
                  (q + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool tfibsegs.

(* ================================ disjointness of region lists ================================ *)
Lemma am_ed_sym : forall E a b, extent_disjoint E a b -> extent_disjoint E b a.
Proof. unfold extent_disjoint. intros E a b H. lia. Qed.
Lemma am_ad_app : forall E r l1 l2, all_disjoint E r l1 -> all_disjoint E r l2 -> all_disjoint E r (l1 ++ l2).
Proof.
intros E r l1 l2 H1 H2. induction l1 as [|x l1 IH]; cbn [app all_disjoint] in *; [exact H2|].
destruct H1 as [Hx H1]. split; [exact Hx | exact (IH H1)].
Qed.
Lemma am_ad_In : forall E r l x, all_disjoint E r l -> In x l -> extent_disjoint E r x.
Proof.
intros E r l x H Hin. induction l as [|y l IH]; cbn in *; [destruct Hin|].
destruct H as [Hy H]. destruct Hin as [<-|Hin]; [exact Hy | exact (IH H Hin)].
Qed.
Lemma am_ad_of : forall E r l, (forall x, In x l -> extent_disjoint E r x) -> all_disjoint E r l.
Proof.
intros E r l H. induction l as [|y l IH]; cbn; [exact I|].
split; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx].
Qed.
Lemma am_pd_app : forall E l1 l2, pairwise_disjoint E l1 -> pairwise_disjoint E l2 ->
Forall (fun r => all_disjoint E r l1) l2 -> pairwise_disjoint E (l1 ++ l2).
Proof.
intros E l1 l2 H1 H2 H12. induction l1 as [|x l1 IH]; cbn [app pairwise_disjoint] in *; [exact H2|].
destruct H1 as [Hx H1]. split.
- apply am_ad_app; [exact Hx|]. apply am_ad_of. intros y Hy. rewrite Forall_forall in H12.
  apply am_ed_sym. pose proof (H12 y Hy) as Hy'. cbn [all_disjoint] in Hy'. exact (proj1 Hy').
- apply IH; [exact H1|]. eapply Forall_impl; [|exact H12]. intros r Hr. cbn [all_disjoint] in Hr. exact (proj2 Hr).
Qed.
Lemma am_ad_prefix : forall E r l1 l2, all_disjoint E r (l1 ++ l2) -> all_disjoint E r l1.
Proof.
intros E r l1 l2 H. induction l1 as [|x l1 IH]; cbn [app all_disjoint] in *; [exact I|].
destruct H as [Hx H]. split; [exact Hx | exact (IH H)].
Qed.
Lemma am_pd_prefix : forall E l1 l2, pairwise_disjoint E (l1 ++ l2) -> pairwise_disjoint E l1.
Proof.
intros E l1 l2 H. induction l1 as [|x l1 IH]; cbn [app pairwise_disjoint] in *; [exact I|].
destruct H as [Hx H]. split; [exact (am_ad_prefix E x l1 l2 Hx) | exact (IH H)].
Qed.
Lemma am_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; cbn [app atoms_ok] in *; [exact H2|].
destruct H1 as [Hf H1]. split; [exact Hf | exact (IH H1)].
Qed.

(* ================================ the environment ================================ *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Definition am_xs (g : ectx) (pos c : Z) : list Z := [FA g pos; shadow_addr (FA g pos); e_p g + c; e_n g - c].
Definition am_env (g : ectx) (pos c : Z) (regs : bvmap 5 word) (ys : list Z) : env :=
Ereg regs (cw_extra (am_xs g pos c ++ ys)).
Lemma am_ew_F : forall g pos c regs ys, ew (am_env g pos c regs ys) 33 = Z_to_bv 64 (FA g pos).
Proof. intros. exact (cw_ew_x regs (am_xs g pos c ++ ys) 0). Qed.
Lemma am_ew_SH : forall g pos c regs ys, ew (am_env g pos c regs ys) 34 = Z_to_bv 64 (shadow_addr (FA g pos)).
Proof. intros. exact (cw_ew_x regs (am_xs g pos c ++ ys) 1). Qed.
Lemma am_ew_CP : forall g pos c regs ys, ew (am_env g pos c regs ys) 35 = Z_to_bv 64 (e_p g + c).
Proof. intros. exact (cw_ew_x regs (am_xs g pos c ++ ys) 2). Qed.
Lemma am_ew_CN : forall g pos c regs ys, ew (am_env g pos c regs ys) 36 = Z_to_bv 64 (e_n g - c).
Proof. intros. exact (cw_ew_x regs (am_xs g pos c ++ ys) 3). Qed.
Lemma am_ew_SB : forall g pos c regs ys, ew (am_env g pos c regs ys) 32 = Z_to_bv 64 SB.
Proof. intros. exact (cw_ew_SB regs (am_xs g pos c ++ ys)). Qed.
(* the segment's own atoms *)
Lemma am_ew_y : forall g pos c regs ys j, ew (am_env g pos c regs ys) (AM_X0 + j) = Z_to_bv 64 (nth j ys 0).
Proof.
intros g pos c regs ys j. unfold am_env, AM_X0. change (37 + j)%nat with (33 + (4 + j))%nat.
rewrite cw_ew_x. reflexivity.
Qed.
Lemma am_ew_reg : forall g pos c regs ys n (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (am_env g pos c regs ys) n = getr regs r.
Proof. intros g pos c regs ys n r H. exact (cw_ew_reg regs _ n r H). Qed.
(* an offset of an atom, as the executor denotes it *)
Lemma am_den_off : forall E n x o, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + o < 2 ^ 64 ->
sv_denot E (SOff n o) = Z_to_bv 64 (x + o).
Proof.
intros E n x o Hn Hx Hxo. cbn [sv_denot]. rewrite Hn. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* ================================ the numbers a cut gives ================================ *)
(* The frame, the machine frame and the input, at any state of the journal from the entry with own = [(3, pos)]. *)
Lemma am_facts : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
frame_addr ly2 3 pos = FA g pos /\ FA g pos mod 64 = 0 /\ 4096 <= FA g pos /\
FA g pos + fs_frame_bytes 3 <= alloc_ceiling /\ 448 <= fs_frame_bytes 3 /\ alloc_ceiling <= AM_HI /\
0x7fff7f800000 <= alloc_ceiling /\
sp1 mod 32 = 0 /\ e_sp0 g - 320 < sp1 <= e_sp0 g - 288 /\ alloc_ceiling + LLVMF_STK <= e_sp0 g /\
e_sp0 g <= 2 ^ 47 /\ e_sp0 g mod 16 = 0 /\
(forall a, e_sp0 g - LLVMF_STK <= a < e_sp0 g -> apresent (w_H W2) mem2 a) /\
0 <= e_n g < 2 ^ 26 /\ 4096 <= e_p g /\ e_p g + e_n g <= AM_HI /\
(0 < e_n g -> In (e_p g, e_n g) (ablocks B ly2 S2) /\ In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g))).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & HSTK & Hceil & Hslo & Hshi & H47 & _).
pose proof HC as (Hpre & Hsp1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (EFA : frame_addr ly2 3 pos = FA g pos).
{ unfold FA, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). lia. }
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (Hf4096 & Hfceil & _).
destruct (frame_al64 tfibsegs B ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (Hf64 & _).
assert (FS3 : 448 <= fs_frame_bytes 3) by (apply Z.leb_le; vm_compute; reflexivity).
rewrite EFA in Hf4096, Hfceil, Hf64.
unfold e_pre, codec_lib_pre_x in Hpre.
destruct Hpre as (HFN & _ & _ & _ & Hpn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HFN as (HAR0 & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hblk : 0 < e_n g -> In (e_p g, e_n g) (ablocks B ly2 S2) /\ In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g))).
{ intros Hn. destruct Hpn as [[Hn0 _] | [_ Hb]]; [lia|]. split; [|exact Hb].
  pose proof HC as HPerm. do 45 (destruct HPerm as (_ & HPerm)).
  eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]. }
assert (Hinput : 0 <= e_n g < 2 ^ 26 /\ 4096 <= e_p g /\ e_p g + e_n g <= AM_HI).
{ destruct Hpn as [[-> ->] | [Hn Hb]]; [unfold A_EMPTY, AM_HI; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hb) as (_ & H4096 & Hbc & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq). unfold AM_HI. lia. }
assert (Hsp : e_sp0 g - 320 < sp1 <= e_sp0 g - 288 /\ sp1 mod 32 = 0).
{ rewrite Hsp1. pose proof (Z.div_mod (e_sp0 g - 288) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (e_sp0 g - 288) 32 ltac:(lia)) as M.
  split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
destruct Hinput as (Hn & Hp & Hpn'). destruct Hsp as ((Hsp1a & Hsp1b) & Hsp32).
unfold AM_HI in *.
split; [exact EFA|]. split; [exact Hf64|]. split; [lia|]. split; [lia|]. split; [exact FS3|].
split; [lia|]. split; [lia|]. split; [exact Hsp32|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [exact Hal16|]. split; [exact Hpres|]. split; [lia|]. split; [lia|]. split; [lia|].
exact Hblk.
Qed.

(* ================================ the base state ================================ *)
Lemma am_base_ok : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c ys,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 <= c <= e_n g ->
regs_ok (am_env g pos c regs2 ys) am_sregs regs2 /\
Forall (region_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2)) am_regs0 /\
pairwise_disjoint (am_env g pos c regs2 ys) am_regs /\
atoms_ok (am_env g pos c regs2 ys) am_atoms.
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c ys HJ Hfr HC Hc.
destruct (am_facts g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & _).
pose proof HJ as (HAR & _). unfold AM_HI in Hchi, Hpn.
destruct HC as (Hpre & Hsp1 & R2 & R9 & R8 & R3 & R4 & R20 & R18 & R21 & R22 & R25 & R19 & R27 & HF64 &
  V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 & _).
set (F := FA g pos) in *.
set (E := am_env g pos c regs2 ys).
assert (EF : ew E 33 = Z_to_bv 64 F) by exact (am_ew_F g pos c regs2 ys).
assert (ESH : ew E 34 = Z_to_bv 64 (shadow_addr F)) by exact (am_ew_SH g pos c regs2 ys).
assert (ECP : ew E 35 = Z_to_bv 64 (e_p g + c)) by exact (am_ew_CP g pos c regs2 ys).
assert (ECN : ew E 36 = Z_to_bv 64 (e_n g - c)) by exact (am_ew_CN g pos c regs2 ys).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (am_ew_SB g pos c regs2 ys).
assert (E2 : ew E 2 = getr regs2 2) by exact (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hsh : SB + 512 <= shadow_addr F <= SB + 2 ^ 44 /\ shadow_addr F mod 8 = 0).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF.
  pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite Hf64, Z.add_0_r in D.
  assert (E8 : F / 8 = 8 * (F / 64)).
  { rewrite D at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  rewrite E8. unfold SB, AM_HI in *. split; [lia|].
  replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia. apply Z.mod_mul. lia. }
split; [|split; [|split]].
- (* the registers *)
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  assert (O9 : getr regs2 9 = sv_denot E (SOff 2 0)) by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E2, R9, R2; reflexivity).
  assert (O18 : getr regs2 18 = sv_denot E (SOff 34 0)) by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ESH, R18; reflexivity).
  assert (O19 : getr regs2 19 = sv_denot E (SOff 33 432)) by (rewrite (am_den_off E 33 F 432 EF) by lia; rewrite R19; reflexivity).
  assert (O20 : getr regs2 20 = sv_denot E (SOff 32 0)) by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32, R20; reflexivity).
  assert (O21 : getr regs2 21 = sv_denot E (SLit 18446744073709551608)).
  { cbn [sv_denot]. rewrite R21. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
  assert (O22 : getr regs2 22 = sv_denot E (SOff 33 176)) by (rewrite (am_den_off E 33 F 176 EF) by lia; rewrite R22; reflexivity).
  assert (O25 : getr regs2 25 = sv_denot E (SOff 33 64)) by (rewrite (am_den_off E 33 F 64 EF) by lia; rewrite R25; reflexivity).
  assert (O27 : getr regs2 27 = sv_denot E (SLit 10)) by (cbn [sv_denot]; rewrite R27; reflexivity).
  repeat (destruct Hr as [<-|Hr];
  [ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
      let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    first [ exact O9 | exact O18 | exact O19 | exact O20 | exact O21 | exact O22 | exact O25 | exact O27
          | cbn [sv_denot];
            first [ rewrite getr_zero; reflexivity
                  | subst E; unfold am_env; rewrite Z.add_0_r, ew_Ereg_lt by lia;
                    match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr _ ?x)) =>
                      let y := eval vm_compute in x in change x with y end;
                    rewrite Z_to_bv_bv_unsigned; reflexivity ] ]
  | ]).
  destruct Hr.
- (* the base regions *)
  apply Forall_app. split.
  + apply (cw_regs_ok B TL LAWS 0 (am_xs g pos c ++ ys) ly2 S2 W2 regs2 mem2 md2 HAR ltac:(lia)).
    * unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
    * intros a Ha. lia.
  + constructor; [|constructor].
    unfold am_spill_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold am_spill_chunks.
    assert (DF : forall o, 0 <= o < 512 -> sv_denot E (SOff 33 o) = Z_to_bv 64 (F + o))
      by (intros o Ho; apply (am_den_off E 33 F o EF); lia).
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val tfibsegs E _ sp1 16 8 (SOff 33 223) (F + 176 + 47)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V16].
    * apply (chunk_ok_val tfibsegs E _ sp1 24 8 (SOff 33 34) (F + 34)); [rewrite DF by lia; reflexivity | zside | zside | exact V24].
    * apply (chunk_ok_val tfibsegs E _ sp1 32 8 (SOff 33 32) (F + 32)); [rewrite DF by lia; reflexivity | zside | zside | exact V32].
    * apply (chunk_ok_val tfibsegs E _ sp1 40 8 (SOff 33 320) (F + 176 + 144)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V40].
    * apply (chunk_ok_val tfibsegs E _ sp1 48 8 (SLit 0x5cb0) 0x5cb0); [reflexivity | zside | zside | exact V48].
    * apply (chunk_ok_val tfibsegs E _ sp1 56 8 (SOff 33 324) (F + 176 + 148)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V56].
    * apply (chunk_ok_val tfibsegs E _ sp1 64 8 (SOff 33 0) F); [rewrite DF by lia; f_equal; lia | zside | zside | exact V64].
    * apply (chunk_ok_val tfibsegs E _ sp1 72 8 (SOff 33 0) F); [rewrite DF by lia; f_equal; lia | zside | zside | exact V72].
    * apply (chunk_ok_val tfibsegs E _ sp1 80 8 (SLit 0x13f0) 0x13f0); [reflexivity | zside | zside | exact V80].
    * apply (chunk_ok_val tfibsegs E _ sp1 88 8 (SOff 33 216) (F + 176 + 40)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V88].
    * apply (chunk_ok_val tfibsegs E _ sp1 96 8 (SOff 33 284) (F + 176 + 108)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V96].
    * apply (chunk_ok_val tfibsegs E _ sp1 104 8 (SOff 33 344) (F + 176 + 168)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V104].
    * apply (chunk_ok_val tfibsegs E _ sp1 112 8 (SLit 0x20f40) CM_DESK); [reflexivity | unfold CM_DESK; zside | zside | exact V112].
    * apply (chunk_ok_val tfibsegs E _ sp1 120 8 (SOff 33 252) (F + 176 + 76)); [rewrite DF by lia; f_equal; lia | zside | zside | exact V120].
- (* the base regions are pairwise disjoint *)
  apply pairwise_disjoint_of_extents.
  unfold am_regs, am_regs0, cw_regs, am_spill_region, am_cur_region, stack_region, got_region, bcell_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U2.
  unfold A_GOT_shadow, A_shadow_glob.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- (* the atom facts *)
  unfold am_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite U2, E32, EF, ESH, ECP, ECN.
  rewrite !unsigned_lit_small by (unfold SB, AM_HI in *; lia).
  change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, AM_HI in *. repeat split; lia.
Qed.

(* ================================ the entry bridge ================================ *)
(* ENTRY BRIDGE. From a cut's components (its journal, frames, mcommon and its cursor) and the segment's own regions
   rs and atom facts AF, the executor state of the segment's start. *)
Lemma am_entry : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c pc ys (rs : smem) (AF : list (nat * afact)),
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
regions_wf rs = true ->
Forall (region_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2)) rs ->
pairwise_disjoint (am_env g pos c regs2 ys) rs ->
Forall (fun r => all_disjoint (am_env g pos c regs2 ys) r am_regs) rs ->
atoms_ok (am_env g pos c regs2 ys) AF ->
st_ok tfibsegs (am_env g pos c regs2 ys) (am_ss pc rs AF)
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c pc ys rs AF HJ Hfr HC Hcur Hwf Hrs Hpd Hap HAF.
pose proof Hcur as (Hc & C152 & C160).
destruct (am_base_ok g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c ys HJ Hfr HC Hc) as (Hregs & Hbase & Hbpd & Hat).
destruct (am_facts g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & Hchi & Hclo & _ & Hsp & Hsp0c & Hsp047 & _ & Hpres & Hn & Hp & Hpn & _).
pose proof HC as (_ & _ & R2 & _).
unfold AM_HI in Hchi, Hpn.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (E2 : ew (am_env g pos c regs2 ys) 2 = getr regs2 2) by exact (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl).
assert (U2 : bv_unsigned (ew (am_env g pos c regs2 ys) 2) = sp1) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold am_ss, am_ssb. apply (entry_st_ok_full tfibsegs).
all: change (Ereg regs2 (cw_extra (am_xs g pos c ++ ys))) with (am_env g pos c regs2 ys).
- exact Hregs.
- rewrite regions_wf_app, Hwf. reflexivity.
- apply Forall_app. split; [|exact Hrs]. unfold am_regs. apply Forall_app. split; [exact Hbase|].
  constructor; [|constructor].
  unfold am_cur_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
  split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
  + constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val tfibsegs (am_env g pos c regs2 ys) _ sp1 152 8 (SOff 35 0) (e_p g + c));
      [rewrite (am_den_off (am_env g pos c regs2 ys) 35 (e_p g + c) 0 (am_ew_CP g pos c regs2 ys)) by (unfold AM_HI in *; lia); f_equal; lia
      | unfold AM_HI in *; zside | zside | exact C152].
    * apply (chunk_ok_val tfibsegs (am_env g pos c regs2 ys) _ sp1 160 8 (SOff 36 0) (e_n g - c));
      [rewrite (am_den_off (am_env g pos c regs2 ys) 36 (e_n g - c) 0 (am_ew_CN g pos c regs2 ys)) by lia; f_equal; lia
      | zside | zside | exact C160].
- apply am_pd_app; [exact Hbpd | exact Hpd | exact Hap].
- split; [apply am_atoms_ok_app; [exact Hat | exact HAF]|]. split; exact I.
Qed.

(* The same without the cursor (EXIT, whose cut carries none): the base am_regs0, the cursor atoms at c = 0. *)
Lemma am_entry0 : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k pc ys (rs : smem) (AF : list (nat * afact)),
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
regions_wf rs = true ->
Forall (region_ok tfibsegs (am_env g pos 0 regs2 ys) (mrestrict (w_H W2) mem2)) rs ->
pairwise_disjoint (am_env g pos 0 regs2 ys) rs ->
Forall (fun r => all_disjoint (am_env g pos 0 regs2 ys) r am_regs0) rs ->
atoms_ok (am_env g pos 0 regs2 ys) AF ->
st_ok tfibsegs (am_env g pos 0 regs2 ys) (am_ss0 pc rs AF)
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k pc ys rs AF HJ Hfr HC Hwf Hrs Hpd Hap HAF.
destruct (am_facts g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
destruct (am_base_ok g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k 0 ys HJ Hfr HC ltac:(lia)) as (Hregs & Hbase & Hbpd & Hat).
rewrite restrict_mkst_fx. unfold am_ss0, am_ssb. apply (entry_st_ok_full tfibsegs).
- exact Hregs.
- rewrite regions_wf_app, Hwf. reflexivity.
- apply Forall_app. split; [exact Hbase | exact Hrs].
- apply am_pd_app; [exact (am_pd_prefix _ _ _ Hbpd) | exact Hpd | exact Hap].
- split; [apply am_atoms_ok_app; [exact Hat | exact HAF]|]. split; exact I.
Qed.


(* ================================ the region builders ================================ *)
Lemma am_mb : forall (W : world tfibsegs) mem a v, aview tfibsegs (w_H W) mem a = Some v ->
mbyte tfibsegs (mrestrict (w_H W) mem) a = Some (Z_to_bv 8 v) /\ 0 <= v < 256.
Proof.
intros W mem a v Hv. destruct (aview_byte tfibsegs (w_H W) mem a v Hv) as (b & Hb & -> & Hr).
split; [rewrite Hb, Z_to_bv_bv_unsigned; reflexivity | exact Hr].
Qed.
Lemma am_shm_len : forall kv, length (shm kv) = 56%nat.
Proof. intros kv. unfold shm. rewrite !length_app, !repeat_length. reflexivity. Qed.
(* the one-byte chunks of a shadow map *)
Lemma am_sh_chunks_ok : forall E (W : world tfibsegs) mem base vs i,
(forall j, 0 <= j < Z.of_nat (length vs) ->
 aview tfibsegs (w_H W) mem (base + (i + j)) = Some (nth (Z.to_nat j) vs 0)) ->
Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) base) (am_sh_chunks vs i).
Proof.
intros E W mem base vs. induction vs as [|v vs IH]; intros i Hj; cbn [am_sh_chunks]; [apply Forall_nil|].
constructor.
- pose proof (Hj 0 ltac:(cbn [length]; lia)) as H0. cbn [Z.to_nat nth] in H0. rewrite Z.add_0_r in H0.
  destruct (am_mb W mem (base + i) v H0) as (Hm & Hr).
  apply (chunk_ok_val tfibsegs E (mrestrict (w_H W) mem) base i 1 (SLit v) v);
  [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
  change (N.to_nat 1) with 1%nat. apply cpg_val_mem1; [lia | exact Hm].
- apply IH. intros j Hjj.
  assert (Hj1 : 0 <= 1 + j < Z.of_nat (length (v :: vs))) by (cbn [length]; lia).
  replace (base + (i + 1 + j)) with (base + (i + (1 + j))) by lia.
  rewrite (Hj (1 + j) Hj1). f_equal.
  replace (Z.to_nat (1 + j)) with (S (Z.to_nat j)) by lia. reflexivity.
Qed.

(* ---- reading one-byte chunks back out of a region (the shadow map after a walk wrote it) ----
   am_sh_find looks a one-byte literal chunk up by offset; am_sh_ok_b checks by computation that a region's
   chunks hold the bytes vs; am_sh_read_all turns that into the cut's `aview ... = Some (nth i vs 0)`. *)
Definition am_sh_find (cs : list YP09.chunk) (i : Z) : option Z :=
match find (fun ch => YP09.c_off ch =? i) cs with
| Some ch => match YP09.c_val ch with CVal 1 (SLit v) => Some (v mod 256) | _ => None end
| None => None
end.
Definition am_sh_ok_b (cs : list YP09.chunk) (vs : list Z) : bool :=
forallb (fun i => match am_sh_find cs (Z.of_nat i) with Some v => v =? nth i vs 0 | None => false end)
        (seq 0 (length vs)).
Lemma am_mod256_64 : forall v, (v mod 18446744073709551616) mod 256 = v mod 256.
Proof.
intros v. symmetry. rewrite (Z.div_mod v 18446744073709551616) at 1 by lia.
replace (18446744073709551616 * (v / 18446744073709551616) + v mod 18446744073709551616)
  with (v mod 18446744073709551616 + 72057594037927936 * (v / 18446744073709551616) * 256) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma am_sh_find_some : forall cs i v, am_sh_find cs i = Some v ->
exists w, In (YP09.mkChunk i (CVal 1 (SLit w))) cs /\ v = w mod 256.
Proof.
intros cs i v H. unfold am_sh_find in H.
destruct (find (fun ch => YP09.c_off ch =? i) cs) as [ch|] eqn:Ef; [|discriminate].
apply find_some in Ef as (Hin & Hb). apply Z.eqb_eq in Hb.
destruct ch as [off cv]. cbn [YP09.c_off YP09.c_val] in Hb, H, Hin. subst off.
destruct cv as [w e | l | l | d s l]; try discriminate H.
destruct w as [|p]; try discriminate H.
destruct p as [p'|p'|]; try discriminate H.
destruct e; try discriminate H.
injection H as <-. exists z. split; [exact Hin | reflexivity].
Qed.
Section r.
Lemma am_sh_read : forall E (W : world tfibsegs) mem r base off v,
region_ok tfibsegs E (mrestrict (w_H W) mem) r -> base_val E (YP09.r_base r) = base ->
In (YP09.mkChunk off (CVal 1 (SLit v))) (YP09.r_chunks r) ->
aview tfibsegs (w_H W) mem (base + off) = Some (v mod 256).
Proof.
intros E W mem r base off v HR Hb Hin.
pose proof (YP09.region_ok_chunk tfibsegs E (mrestrict (w_H W) mem) r _ HR Hin) as Hck.
rewrite Hb in Hck.
pose proof (val_of_chunk_any tfibsegs E (mrestrict (w_H W) mem) base off 1 (SLit v) Hck ltac:(cbn; lia)) as HV.
assert (EV : bv_unsigned (sv_denot E (SLit v)) mod 2 ^ (8 * Z.of_N 1) = v mod 256).
{ cbn [sv_denot]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. change (2 ^ (8 * Z.of_N 1)) with 256.
  apply am_mod256_64. }
rewrite EV in HV.
apply (aview_of_val_mem1 tfibsegs (w_H W) mem (base + off) (v mod 256)); [exact HV|].
apply Z.mod_pos_bound. lia.
Qed.
Lemma am_sh_read_all : forall E (W : world tfibsegs) mem r base vs,
region_ok tfibsegs E (mrestrict (w_H W) mem) r -> base_val E (YP09.r_base r) = base ->
am_sh_ok_b (YP09.r_chunks r) vs = true ->
forall i, 0 <= i < Z.of_nat (length vs) ->
aview tfibsegs (w_H W) mem (base + i) = Some (nth (Z.to_nat i) vs 0).
Proof.
intros E W mem r base vs HR Hb Hok i Hi.
assert (Hin : In (Z.to_nat i) (seq 0 (length vs))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hok (Z.to_nat i) Hin) as Hf. cbn beta in Hf.
rewrite Z2Nat.id in Hf by lia.
destruct (am_sh_find (YP09.r_chunks r) i) as [v|] eqn:Ef; [|discriminate].
apply Z.eqb_eq in Hf.
destruct (am_sh_find_some _ _ _ Ef) as (w & Hinc & ->).
rewrite <- Hf. exact (am_sh_read E W mem r base i w HR Hb Hinc).
Qed.
End r.

(* (b) the frame's 56 shadow bytes, writable in [wlo, whi) *)
Lemma am_shadow_region_ok : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c ys wlo whi,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 <= wlo -> whi <= 56 ->
region_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (am_shadow_region wlo whi (shm kv)).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c ys wlo whi HJ Hfr HC Hwlo Hwhi.
destruct (am_facts g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & _).
unfold AM_HI in Hchi.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & _ & Hsh).
rewrite EFA in Hsh.
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
assert (Hd1 : 0 <= FA g pos / 8 <= FA g pos) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HB : base_val (am_env g pos c regs2 ys) (Some 34%nat) = shadow_addr (FA g pos)).
{ cbn [base_val]. rewrite (am_ew_SH g pos c regs2 ys). apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
unfold am_shadow_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite HB.
split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [unfold shadow_addr, SHADOW_OFF; lia|]. split.
- intros o Ho. apply (apresent_writable tfibsegs). apply Hsh.
  change (fs_frame_bytes 3 / 8) with 64. lia.
- apply (am_sh_chunks_ok _ W2 mem2). intros j Hj. rewrite am_shm_len in Hj.
  rewrite Z.add_0_l. apply HSH'. lia.
Qed.

(* (a) / (c) a range of the frame with the chunks the segment gives: k = F + 176 (184 bytes), text = F + 64
   (65), SCRIBBLE's payload F + 32 (10), the dots byte F + 432 *)
Lemma am_frame_region_ok : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c ys lo hi wlo whi cs,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 <= lo -> lo <= hi -> hi <= 448 -> lo <= wlo -> whi <= hi ->
Forall (YP09.chunk_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (FA g pos)) cs ->
region_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (am_frame_region lo hi wlo whi cs).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c ys lo hi wlo whi cs HJ Hfr HC Hlo Hlh Hhi Hwl Hwh Hcs.
destruct (am_facts g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & _).
unfold AM_HI in Hchi.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Hpr & _).
rewrite EFA in Hpr.
assert (HB : base_val (am_env g pos c regs2 ys) (Some 33%nat) = FA g pos).
{ cbn [base_val]. rewrite (am_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
unfold am_frame_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite HB.
split; [lia|]. split; [lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable tfibsegs).
exact (proj1 (Hpr (FA g pos + o) ltac:(change (fs_frame_bytes 3) with 512; lia))).
Qed.

(* (e) the input block: the cursor's bytes are marked usable, and the engine's shadow entry for them *)
Lemma am_cur_ra : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c n,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 <= c -> 0 <= n -> c + n <= e_n g ->
range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (e_p g + c) n.
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c n HJ Hfr HC Hc Hn Hcn.
destruct (am_facts g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hng & _ & _ & Hblk).
destruct (Z_le_gt_dec n 0) as [Hn0|Hnp]; [apply range_addressable_nil; lia|].
destruct (Hblk ltac:(lia)) as (Hin2 & _).
pose proof HJ as (HAR & _).
destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR Hin2) as (HBS & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
exact (block_shadow_range (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (e_p g) (req_size (e_n g))
  (e_p g + c) n HBS ltac:(lia) ltac:(lia)).
Qed.
Lemma am_cur_shent : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c ys n,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 <= c -> 0 < n -> c + n <= e_n g ->
shent_ok tfibsegs CW_Bx (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (mkSHE 35 0 n).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c ys n HJ Hfr HC Hc Hn Hcn.
destruct (am_facts g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & Hchi & Hclo & _ & _ & _ & _ & _ & _ & Hng & Hp & Hpn & Hblk).
unfold AM_HI in Hchi, Hpn.
pose proof (am_cur_ra g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k c n HJ Hfr HC Hc ltac:(lia) Hcn) as Hra.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (Hblk ltac:(lia)) as (Hin2 & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR Hin2) as (_ & H4096 & Hbc & Happ & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
assert (Ham : amem_range (e_p g + c) n) by (appn; lia).
apply (cw_shent_ra W2 mem2 (am_env g pos c regs2 ys) 35 (e_p g + c) n Hra Ham).
- lia.
- lia.
- lia.
- exact (am_ew_CP g pos c regs2 ys).
- exact (am_ew_SB g pos c regs2 ys).
Qed.

(* ================================ the shadow maps the call sites consume ================================ *)
Lemma am_block_shadow : forall (W : world tfibsegs) mem F off n,
F mod 64 = 0 -> 0 <= off -> off mod 8 = 0 -> 0 <= n ->
(forall i, 0 <= i < (n + 7) / 8 ->
 aview tfibsegs (w_H W) mem (shadow_addr F + (off / 8 + i)) = Some (if i <? n / 8 then 0 else n mod 8)) ->
block_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + off) n.
Proof.
intros W mem F off n H64 Hoff Ho8 Hn HS.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite H64, Z.add_0_r in D.
  replace F with ((8 * (F / 64)) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
pose proof (Z.div_mod off 8 ltac:(lia)) as DO. rewrite Ho8, Z.add_0_r in DO.
assert (ED : (F + off) / 8 = F / 8 + off / 8).
{ replace (F + off) with ((F / 8 + off / 8) * 8) by lia. apply Z.div_mul. lia. }
split; [|split; [exact Hn|]].
- replace (F + off) with ((F / 8 + off / 8) * 8) by lia. apply Z_mod_mult.
- intros i Hi. unfold shadow_of_addr. rewrite ED.
  replace (SHADOW_OFF + (F / 8 + off / 8) + i) with (shadow_addr F + (off / 8 + i))
    by (unfold shadow_addr; lia).
  exact (HS i Hi).
Qed.
(* the call record k (184 bytes at F + 176) when its 23 shadow bytes are 0 *)
Lemma am_bs_k : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2,
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
block_shadow (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + 176) 184.
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 HC.
pose proof HC as HF64. do 14 (destruct HF64 as (_ & HF64)). destruct HF64 as (HF64 & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
apply am_block_shadow; [exact HF64 | lia | reflexivity | lia |].
intros i Hi. change ((184 + 7) / 8) with 23 in Hi. change (184 / 8) with 23. change (176 / 8) with 22.
rewrite (proj2 (Z.ltb_lt i 23) ltac:(lia)).
rewrite (HSH' (22 + i) ltac:(lia)). f_equal.
pose proof amain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _).
apply (Hk23 0 (Z.to_nat (22 + i))). lia.
Qed.
(* text[65] at F + 64 (its 8 whole granules and the partial one) *)
Lemma am_bs_text : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2,
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
block_shadow (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + 64) 65.
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 HC.
pose proof HC as HF64. do 14 (destruct HF64 as (_ & HF64)). destruct HF64 as (HF64 & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
pose proof amain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & _ & H8_16 & H16 & _).
apply am_block_shadow; [exact HF64 | lia | reflexivity | lia |].
intros i Hi. change ((65 + 7) / 8) with 9 in Hi. change (65 / 8) with 8. change (64 / 8) with 8.
change (65 mod 8) with 1.
rewrite (HSH' (8 + i) ltac:(lia)).
destruct (Z.ltb_spec i 8) as [Hlt|Hge]; f_equal.
- apply (H8_16 kv (Z.to_nat (8 + i))). lia.
- assert (Ei : i = 8) by lia. subst i. change (Z.to_nat (8 + 8)) with 16%nat. apply H16.
Qed.
(* the dots byte at F + 432, when the walk has marked its shadow byte 01 *)
Lemma am_bs_dots : forall (W : world tfibsegs) mem F,
F mod 64 = 0 -> aview tfibsegs (w_H W) mem (shadow_addr F + 54) = Some 1 ->
block_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 432) 1.
Proof.
intros W mem F H64 H54. apply am_block_shadow; [exact H64 | lia | reflexivity | lia |].
intros i Hi. change ((1 + 7) / 8) with 1 in Hi. change (1 / 8) with 0. change (432 / 8) with 54.
change (1 mod 8) with 1. assert (Ei : i = 0) by lia. subst i.
rewrite (proj2 (Z.ltb_ge 0 0) ltac:(lia)). rewrite Z.add_0_r. exact H54.
Qed.

(* ================================ the exit bridge ================================ *)
(* the bytes a segment must not have written for the cut's kept facts to carry *)
Definition am_keepzone (g : ectx) (pos sp1 a : Z) : Prop :=
(sp1 + 16 <= a < sp1 + 128) \/ (e_sp0 g - 104 <= a < e_sp0 g) \/
(FA g pos + 504 <= a < FA g pos + 512).

(* EXIT BRIDGE. From a segment's final executor state, its journal and the kept-memory fact of the run, the
   mcommon of the end cut: the registers read off the state, the spills / saves / flag word / input bytes
   kept, the frame's shadow bytes as the segment leaves them. *)
Lemma am_exit : forall g pos sp1 kv kv' c ys ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 k3 pcv ss E,
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
env_agree 35 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W3) (mkst regs3 pcv mem3 (seg_rom tfibsegs))) ->
am_keep_ok (ss_regs ss) = true ->
(forall a, am_keepzone g pos sp1 a -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
(forall i, 0 <= i < 56 ->
 aview tfibsegs (w_H W3) mem3 (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm kv') 0)) ->
Permutation (ablocks B ly3 S3) (ablocks B (e_ly g) (e_S g)) ->
mcommon B MT K XM_LIB g pos sp1 kv' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros g pos sp1 kv kv' c ys ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 k3 pcv ss E
  HC HJ3 HAE HS Hkeep KE HSH HPerm.
pose proof (proj1 HAE) as AG.
destruct HC as (Hpre & Hsp1 & R2 & R9 & R8 & R3 & R4 & R20 & R18 & R21 & R22 & R25 & R19 & R27 & HF64 &
  V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 &
  S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & SFL & _ & Hga & _).
pose proof Hpre as HPRE0. unfold e_pre, codec_lib_pre_x in HPRE0.
destruct HPRE0 as (HFN & _ & _ & _ & Hpn & Hnpl & HPL & Hfr0 & _).
pose proof HFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK & Hceil0 & Hslo0 & Hshi0 & H470 & _).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hfr3 : frames S3 = [(3, pos)]) by (rewrite Hfrs3, Hfr0; reflexivity).
assert (Hin3 : In (3, pos) (frames S3)) by (rewrite Hfr3; left; reflexivity).
assert (EFA3 : frame_addr ly3 3 pos = FA g pos).
{ unfold FA, frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). lia. }
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 mem3 md3 3 pos HAR3 Hin3) as (Hf4096 & Hfceil & _).
rewrite EFA3 in Hf4096, Hfceil.
assert (FS3 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity). rewrite FS3 in Hfceil.
assert (Hsp : e_sp0 g - 320 < sp1 <= e_sp0 g - 288).
{ rewrite Hsp1. pose proof (Z.div_mod (e_sp0 g - 288) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (e_sp0 g - 288) 32 ltac:(lia)) as M. lia. }
assert (Hsp0 : alloc_ceiling + LLVMF_STK <= e_sp0 g /\ e_sp0 g <= 2 ^ 47) by (unfold e_sp0 in *; lia).
destruct Hsp0 as (Hsp0a & Hsp0b).
assert (Hinp : 0 <= e_n g < 2 ^ 26 /\ 4096 <= e_p g /\ e_p g + e_n g <= 0x7fffff800000).
{ destruct Hpn as [[-> ->] | [Hn Hb]]; [unfold A_EMPTY; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hb) as (_ & H4096 & Hbc & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq). lia. }
destruct Hinp as (Hng & Hpg & Hpng).
assert (RR : forall (r : bv 5), In r AM_KEEPR -> getr regs3 r = sv_denot E (sr_get am_sregs r)).
{ intros r Hr. pose proof (proj1 (forallb_forall _ _) Hkeep r Hr) as Hb.
  apply sv_eqb_eq in Hb. rewrite <- Hb.
  exact (st_ok_restrict_reg tfibsegs (w_H W3) E ss
    (mkst regs3 pcv mem3 (seg_rom tfibsegs)) r HS). }
assert (EF : ew E 33 = Z_to_bv 64 (FA g pos))
  by (rewrite (AG 33%nat ltac:(lia)); exact (am_ew_F g pos c regs2 ys)).
assert (ESH : ew E 34 = Z_to_bv 64 (shadow_addr (FA g pos)))
  by (rewrite (AG 34%nat ltac:(lia)); exact (am_ew_SH g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (rewrite (AG 32%nat ltac:(lia)); exact (am_ew_SB g pos c regs2 ys)).
assert (DOF : forall o, 0 <= o <= 512 -> sv_denot E (SOff 33 o) = w64 (FA g pos + o)).
{ intros o Ho. unfold w64. apply (am_den_off _ 33 (FA g pos) o EF); lia. }
assert (DAT : forall n (r : bv 5), (n < 35)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot E (SOff n 0) = getr regs2 r).
{ intros n r Hn Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite (AG n Hn). apply am_ew_reg. exact Hr. }
assert (VM : forall a m v, (forall i, 0 <= i < Z.of_nat m -> am_keepzone g pos sp1 (a + i)) ->
  0 <= a -> a + Z.of_nat m <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a m v -> val_mem tfibsegs (mrestrict (w_H W3) mem3) a m v).
{ intros a m v Hin Ha Ham Hv. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
  intros x Hx. apply KE. replace x with (a + (x - a)) by lia. apply Hin. lia. }
assert (SPZ : forall o, 16 <= o <= 120 -> forall i, 0 <= i < Z.of_nat 8 -> am_keepzone g pos sp1 (sp1 + o + i))
  by (intros o Ho i Hi; left; cbn in Hi; lia).
assert (SVZ : forall o, 8 <= o <= 104 -> forall i, 0 <= i < Z.of_nat 8 -> am_keepzone g pos sp1 (e_sp0 g - o + i))
  by (intros o Ho i Hi; right; left; cbn in Hi; lia).
assert (G2 : sr_get am_sregs 2%bv = SOff 2 0) by (vm_compute; reflexivity).
assert (G9 : sr_get am_sregs 9%bv = SOff 2 0) by (vm_compute; reflexivity).
assert (G8 : sr_get am_sregs 8%bv = SOff 8 0) by (vm_compute; reflexivity).
assert (G3 : sr_get am_sregs 3%bv = SOff 3 0) by (vm_compute; reflexivity).
assert (G4 : sr_get am_sregs 4%bv = SOff 4 0) by (vm_compute; reflexivity).
assert (G20 : sr_get am_sregs 20%bv = SOff 32 0) by (vm_compute; reflexivity).
assert (G18 : sr_get am_sregs 18%bv = SOff 34 0) by (vm_compute; reflexivity).
assert (G21 : sr_get am_sregs 21%bv = SLit 18446744073709551608) by (vm_compute; reflexivity).
assert (G22 : sr_get am_sregs 22%bv = SOff 33 176) by (vm_compute; reflexivity).
assert (G25 : sr_get am_sregs 25%bv = SOff 33 64) by (vm_compute; reflexivity).
assert (G19 : sr_get am_sregs 19%bv = SOff 33 432) by (vm_compute; reflexivity).
assert (G27 : sr_get am_sregs 27%bv = SLit 10) by (vm_compute; reflexivity).
unfold mcommon.
split; [exact Hpre|]. split; [exact Hsp1|].
split; [rewrite (RR 2%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G2, (DAT 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
split; [rewrite (RR 9%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G9, (DAT 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
split; [rewrite (RR 8%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G8, (DAT 8%nat 8%bv ltac:(lia) eq_refl); exact R8|].
split; [rewrite (RR 3%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G3, (DAT 3%nat 3%bv ltac:(lia) eq_refl); exact R3|].
split; [rewrite (RR 4%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G4, (DAT 4%nat 4%bv ltac:(lia) eq_refl); exact R4|].
split; [rewrite (RR 20%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G20; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RR 18%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G18; cbn [sv_denot]; rewrite ESH, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RR 21%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G21; cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
split; [rewrite (RR 22%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G22, (DOF 176 ltac:(lia)); reflexivity|].
split; [rewrite (RR 25%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G25, (DOF 64 ltac:(lia)); reflexivity|].
split; [rewrite (RR 19%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G19, (DOF 432 ltac:(lia)); reflexivity|].
split; [rewrite (RR 27%bv ltac:(unfold AM_KEEPR; cbn [In]; tauto)), G27; cbn [sv_denot]; reflexivity|].
split; [exact HF64|].
split; [apply (VM _ 8%nat); [apply (SPZ 16); lia | lia | cbn; lia | exact V16]|].
split; [apply (VM _ 8%nat); [apply (SPZ 24); lia | lia | cbn; lia | exact V24]|].
split; [apply (VM _ 8%nat); [apply (SPZ 32); lia | lia | cbn; lia | exact V32]|].
split; [apply (VM _ 8%nat); [apply (SPZ 40); lia | lia | cbn; lia | exact V40]|].
split; [apply (VM _ 8%nat); [apply (SPZ 48); lia | lia | cbn; lia | exact V48]|].
split; [apply (VM _ 8%nat); [apply (SPZ 56); lia | lia | cbn; lia | exact V56]|].
split; [apply (VM _ 8%nat); [apply (SPZ 64); lia | lia | cbn; lia | exact V64]|].
split; [apply (VM _ 8%nat); [apply (SPZ 72); lia | lia | cbn; lia | exact V72]|].
split; [apply (VM _ 8%nat); [apply (SPZ 80); lia | lia | cbn; lia | exact V80]|].
split; [apply (VM _ 8%nat); [apply (SPZ 88); lia | lia | cbn; lia | exact V88]|].
split; [apply (VM _ 8%nat); [apply (SPZ 96); lia | lia | cbn; lia | exact V96]|].
split; [apply (VM _ 8%nat); [apply (SPZ 104); lia | lia | cbn; lia | exact V104]|].
split; [apply (VM _ 8%nat); [apply (SPZ 112); lia | lia | cbn; lia | exact V112]|].
split; [apply (VM _ 8%nat); [apply (SPZ 120); lia | lia | cbn; lia | exact V120]|].
split; [apply (VM _ 8%nat); [apply (SVZ 8); lia | lia | cbn; lia | exact S8]|].
split; [apply (VM _ 8%nat); [apply (SVZ 16); lia | lia | cbn; lia | exact S16]|].
split; [apply (VM _ 8%nat); [apply (SVZ 24); lia | lia | cbn; lia | exact S24]|].
split; [apply (VM _ 8%nat); [apply (SVZ 32); lia | lia | cbn; lia | exact S32]|].
split; [apply (VM _ 8%nat); [apply (SVZ 40); lia | lia | cbn; lia | exact S40]|].
split; [apply (VM _ 8%nat); [apply (SVZ 48); lia | lia | cbn; lia | exact S48]|].
split; [apply (VM _ 8%nat); [apply (SVZ 56); lia | lia | cbn; lia | exact S56]|].
split; [apply (VM _ 8%nat); [apply (SVZ 64); lia | lia | cbn; lia | exact S64]|].
split; [apply (VM _ 8%nat); [apply (SVZ 72); lia | lia | cbn; lia | exact S72]|].
split; [apply (VM _ 8%nat); [apply (SVZ 80); lia | lia | cbn; lia | exact S80]|].
split; [apply (VM _ 8%nat); [apply (SVZ 88); lia | lia | cbn; lia | exact S88]|].
split; [apply (VM _ 8%nat); [apply (SVZ 96); lia | lia | cbn; lia | exact S96]|].
split; [apply (VM _ 8%nat); [apply (SVZ 104); lia | lia | cbn; lia | exact S104]|].
split; [apply (VM _ 8%nat); [intros i Hi; right; right; cbn in Hi; lia | lia | cbn; lia | exact SFL]|].
split; [exact HSH|].
split.
- (* the input bytes: the journal keeps them (its footprint is empty) *)
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  intros j Hj. pose proof Hj as Hj'. rewrite length_map in Hj'.
  destruct (HPL j Hj) as (Hv & Hr). split; [|exact Hr].
  assert (Hn0 : 0 < e_n g) by lia.
  assert (Hin0 : In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)))
    by (destruct Hpn as [[Hz _] | [_ Hb]]; [lia | exact Hb]).
  assert (Hinb3 : In (e_p g, e_n g) (ablocks B ly3 S3))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hin0]).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
  apply (cw_val_mem_kept (w_H (e_W g)) (w_H W3) (e_mem g) mem3); [|exact Hv].
  intros x Hx. cbn [Z.of_nat] in Hx.
  replace x with (e_p g + (x - e_p g)) by lia.
  apply (F2 (e_p g) (e_n g) (x - e_p g) Hin0 Hinb3); [lia | apply inFP_nil].
- exact HPerm.
Qed.

(* the cut from its parts: the journal, the frames, the budget, the meter and mcommon *)
Lemma am_mcut : forall g pos sp1 kv pc P ly3 S3 W3 regs3 mem3 md3 k3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
frames S3 = [(3, pos)] -> 0 <= k3 <= EV_LIB -> mo_le MT (e_S g) S3 0 ->
mcommon B MT K XM_LIB g pos sp1 kv ly3 S3 W3 regs3 mem3 md3 ->
P ly3 S3 W3 regs3 mem3 md3 ->
mcut B MT K XM_LIB g pos sp1 kv pc P W3 (cfg_at tfibsegs pc regs3 mem3 md3).
Proof.
intros g pos sp1 kv pc P ly3 S3 W3 regs3 mem3 md3 k3 HJ Hfr Hk Hmo HC HP.
exists ly3, S3, regs3, mem3, md3, k3.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hk|].
split; [exact Hmo|]. split; [exact HC | exact HP].
Qed.

(* the read-only ranges of the image tables, for CPgWalkImg's cpg_img_region_ok *)
Lemma am_in_ro : forall q n, am_ro_b q n = true -> forall a, q <= a < q + n -> in_roP tfibsegs CA_RLO CA_RHI a.
Proof.
intros q n Hb a Ha. unfold am_ro_b in Hb. apply existsb_exists in Hb as (s & Hin & Hc).
apply andb_prop in Hc as (Hc & Hhi). apply andb_prop in Hc as (Hw & Hlo).
apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
left. exists s. split; [exact Hin|]. split; [exact Hw | lia].
Qed.
End b.
End a.
