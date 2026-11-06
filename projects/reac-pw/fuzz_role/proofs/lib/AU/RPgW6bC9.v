(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v at 527e8d2097d9,
   proofs/reac-pw/fuzz_role/lib/A/RPgW6aTail.v at e261793226b4 and proofs/reac-pw/fuzz_role/lib/A/RPgW6aC2h.v at
   616508a91de2 for reac-pw/fuzz_rate's image A: module paths changed; their helpers (the register and chunk readers
   of a run's last state, the leaf of a run, the call of __asan_memcpy) are restated over rate's kit (RtPgSteps'
   rts_post / rts_intrin_seq / rts_post_seq, RtPgMem's rtm_bytes) for a new block lemma, rate's case 9. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC9.v at 32f84792c2a6; for image B
   (fuzz_rate.asan-ubsan): every pc, register, real-frame cell and data address is image B's; the pod object is e62
   at F + 0x210 in the class-4 frame for locals (1024 bytes); the head's run also decides the two UBSan
   pointer-overflow tests 0x81aac and 0x81ac8 from its atom ranges; the tail moves the cursor and what is left into
   s10 and t1 and reloads s2; the kit is RtPgStepsB / RtPgMemB and the statement is RtPgW6bBaseB's w6bb_c9_stmt. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6bC9B.v at a191d52e2a9a for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths changed (lib/AU/Img0.rsegs, lib/A/RPgBase and
   RPgCSpec, lib/AU/RPgSteps.v rl_ and lib/AU/RPgMem.v rm_ names); every pc, real-frame cell and data address is
   role B's: the head reads &e62 from [R+0x158], &e62.body from [R+0x110] (once, into a2, for both pointer-overflow
   tests 0x812ec and 0x81304) and &e62.body[8] from [R+0x48]; ent_build.s is 0x21160 and checked_memcpy 0x5116c
   (ra 0x81320); the tail stores the size through [R+0x158] and sets t1 := s6, a3 := s2, s6 := [R+0x130],
   a5 := [R+0x140] (three cells, one more atom); the real frame is 0x200 bytes; the statement is
   lib/AU/RPgW6bBase.v's w6bb_c9_stmt. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the block lemma w6bb_c9 of
   lib/AU/RPgW6bBase.v, case 9 of ent_build's `switch (kind % 10)` (pod.h:367-377) inside LLVMFuzzerTestOneInput
   (0x80020), from the case entry W6BB_D9 0x812d4 to the join J 0x818d8. Proves no function (kind: segment lemma):
   checked_memcpy is the Section hypothesis AMEMCPY (the kernel's YG0d.aintrin_realizes at 0x5116c).

   THE CODE (image B):
     0x812d4  ld a0,0x158(s1) (= F + 0x210, &e62); a1 := 14; sw a1,0(a0) (e62.type); sw a1,8(a0) (e62.body[0..4))
     0x812e4  a0 := -5; ld a2,0x110(s1) (= F + 0x218, &e62.body); 0x812ec bgeu a0,a2 -> 0x812f4 (else the UBSan trap
              `j 0x82604` at 0x812f0): taken, as &e62.body + 4 does not wrap
     0x812f4  ld a0,0x158(s1); a1 := 8; sw a1,0xc(a0) (e62.body[4..8))
     0x81300  a0 := -9; 0x81304 bgeu a0,a2 -> 0x8130c (else the trap `j 0x82604` at 0x81308): taken
     0x8130c  a1 := 0x21160 (ent_build.s; auipc, addi); a2 := 14; ld a0,0x48(s1) (= F + 0x220, &e62.body[8])
     0x8131c  jal checked_memcpy 0x5116c (ra = 0x81320): e62.body[8..22) := "reac.cfg.rate" and its NUL
     0x81320  ld a0,0x158(s1); a1 := 0x18; sw a1,4(a0) (e62.size = 24); j 0x81584
     0x81584  t1 := s6; a3 := s2; ld s6,0x130(s1) (= pp + 0x4000); j 0x81740
     0x81740  ld a5,0x140(s1) (= pp); j J 0x818d8
   No input byte is read and no instrumented check runs; the stores into e62 carry no check. s2 (the cursor) and s6
   (what is left) are callee-saved, so the call keeps them for the tail.

   THE PROOF is three blocks, chained by lib/AU/RPgSteps.v's rl_intrin_seq and rl_wpost_seq:
     c9b_head  0x812d4 .. 0x5116c, one engine run. The real-frame cells [R+0x48], [R+0x110] and [R+0x158] are one
               read-only region based at s1 (their values the extra env slots 33, 34 and 32); e62 is a region based
               at slot 32 whose one chunk is CZero 104 (w6bb_in) and whose write window [0, 16) lies in the frame
               (4, pos) the harness owns (rl_awr_ok_fobj). Slot 34's range [4096, 2 ^ 47] (closed numerals)
               decides both `bgeu` tests: the trap branches 0x812ec and 0x81304 are refuted by the run.
               The run's last chunks give e62's 104 bytes.
     the call  rl_intrin_seq OCpy: the destination's write right and shadow facts are e62's, the source's are
               w6bb_s_ok (rl_cstr at 0x21160); both are carried over the head's stores, which write e62 only:
               shadow bytes lie in the shadow band (rm_shadow_not_app, c9b_hull_out), and no byte of the image
               lies in a frame (AR's client-image law).
     c9b_tail  0x81320 .. J, one engine run: [R+0x130], [R+0x140] and [R+0x158] based at s1 (slots 33, 34 and 32),
               e62's size word based at slot 32.
   e62's bytes at J are the head's, patched by the call's copy and the tail's store (rm_bytes_patch,
   rm_bytes_store): Layout.ent_mem of Model.ent_build's kind-9 pod. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSteps RPgMem RPgW6bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the blocks' states ======================================== *)
Definition C9B_RET : Z := 0x81320.     (* after the jal of checked_memcpy *)
(* the head: [R+0x48] = F + 0x220 (slot 33), [R+0x110] = F + 0x218 (slot 34), [R+0x158] = F + 0x210 (slot 32); e62
   at slot 32, 104 zero bytes. Every atom bound is a closed term: slot 34's upper bound decides 0x812ec and 0x81304. *)
Definition c9b_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0x48 0x160 0 0
  [YP09.mkChunk 0x48 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x110 (CVal 8 (SOff 34 0));
   YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))].
Definition c9b_rE : YP09.region := YP09.mkRegion (Some 32%nat) 0 104 0 16 [YP09.mkChunk 0 (CZero 104)].
Definition c9b_facts1 : facts :=
  mkFacts [(9%nat, mkAF 4096 (2 ^ 47) 4); (32%nat, mkAF 4096 (2 ^ 47) 4); (33%nat, mkAF 4096 (2 ^ 47) 4);
           (34%nat, mkAF 4096 (2 ^ 47) 3)] [] [].
Definition c9b_ss1 : sstate := mkSS W6BB_D9 sr_atoms [c9b_rR; c9b_rE] None c9b_facts1.
Definition c9b_extra1 (F : Z) : list word := [w64 (F + 0x210); w64 (F + 0x220); w64 (F + 0x218)].
(* the tail: [R+0x130] = pp + 0x4000 (slot 33), [R+0x140] = pp (slot 34), [R+0x158] = F + 0x210 (slot 32); e62's
   size word at slot 32 *)
Definition c9b_rS : YP09.region := YP09.mkRegion (Some 9%nat) 0x130 0x160 0 0
  [YP09.mkChunk 0x130 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x140 (CVal 8 (SOff 34 0));
   YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))].
Definition c9b_rZ : YP09.region := YP09.mkRegion (Some 32%nat) 4 8 4 8 [].
Definition c9b_facts3 : facts := mkFacts [(9%nat, mkAF 4096 (2 ^ 47) 4); (32%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
Definition c9b_ss3 : sstate := mkSS C9B_RET sr_atoms [c9b_rS; c9b_rZ] None c9b_facts3.
Definition c9b_extra3 (F q p : Z) : list word := [w64 (F + 0x210); w64 q; w64 p].

(* e62's bytes after the head, after the call, and the pod (Model.ent_build, kind % 10 = 9) *)
Definition c9b_L1 : list byte := le32 14 ++ zeros 4 ++ le32 14 ++ le32 8 ++ zeros 88.
Definition c9b_L2 : list byte := Model.overwrite c9b_L1 16 (S9 ++ [NUL]).
Definition c9b_ent : ent := Ent POD_STRUCT 24 (le32 14 ++ le32 POD_STRING ++ S9 ++ [NUL] ++ zeros 2).
Lemma c9b_ent_mem : map (fun x : byte => bv_unsigned x) (ent_mem c9b_ent) =
  map (fun x : byte => bv_unsigned x) (Model.overwrite c9b_L2 4 (le32 24)).
Proof. vm_compute. reflexivity. Qed.
Lemma c9b_ent_build : forall (b : byte) r, bv_unsigned b mod 10 = 9 -> ent_build (b :: r) = (c9b_ent, r).
Proof. intros b r H. unfold ent_build. cbn [fuzz_u8]. rewrite H. reflexivity. Qed.
(* the head's write window: e62's type, size and body[0..8) *)
Definition c9b_e16 (F a : Z) : Prop := F + 0x210 <= a < F + 0x220.

Lemma c9b_ret_ok : YK0s.ret_ok (w64 C9B_RET).
Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

(* ======================================== small helpers ======================================== *)
Lemma c9b_nz : forall r : bv 5, (bv_unsigned r =? 0) = false -> bv_unsigned r <> 0.
Proof. intros r H. apply Z.eqb_neq. exact H. Qed.
Lemma c9b_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l H Hin. induction l as [|c l IH]; [exact Hin|]. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)]. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate H1.
Qed.
Lemma c9b_incl : forall l l' : list (bv 5), forallb (fun r => existsb (fun c => bv_eqb c r) l') l = true ->
forall r, In r l -> In r l'.
Proof.
intros l l' H r Hr. rewrite forallb_forall in H. specialize (H r Hr).
apply existsb_exists in H as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact Hc.
Qed.
Lemma c9b_mod16 : forall F o, F mod 32 = 0 -> o mod 16 = 0 -> (F + o) mod 16 = 0.
Proof.
intros F o HF Ho. apply (proj1 (Z.mod_divide F 32 ltac:(lia))) in HF. destruct HF as [q ->].
replace (q * 32 + o) with (o + (2 * q) * 16) by ring. rewrite Z.mod_add by lia. exact Ho.
Qed.
Lemma c9b_mod8 : forall F o, F mod 32 = 0 -> o mod 8 = 0 -> (F + o) mod 8 = 0.
Proof.
intros F o HF Ho. apply (proj1 (Z.mod_divide F 32 ltac:(lia))) in HF. destruct HF as [q ->].
replace (q * 32 + o) with (o + (4 * q) * 8) by ring. rewrite Z.mod_add by lia. exact Ho.
Qed.
Lemma c9b_faddr : forall n1 n2 ly ly1 lyc cid pos, layout_le n1 ly ly1 -> layout_le n2 ly lyc ->
frame_addr ly1 cid pos = frame_addr lyc cid pos.
Proof.
intros n1 n2 ly ly1 lyc cid pos (_ & _ & _ & _ & _ & F1 & _) (_ & _ & _ & _ & _ & F2 & _).
unfold frame_addr. rewrite F1, F2. reflexivity.
Qed.
Ltac c9b_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; c9b_kio].
Ltac c9b_in := cbn [In]; repeat (first [left; reflexivity | right]).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* an entry atom: a register of the entry, or an extra env slot *)
Lemma c9b_atom : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
intros regs extra n r Hn. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regs extra n r Hn), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
unfold M64. lia.
Qed.
Lemma c9b_xatom : forall regs extra j n, n = (32 + j)%nat ->
sv_denot (Ereg regs extra) (SOff n 0) = nth j extra (Z_to_bv 64 0).
Proof.
intros regs extra j n ->. apply bv_eq. rewrite denot_SOff, ew_Ereg_extra, Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (nth j extra (Z_to_bv 64 0))) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.
Lemma c9b_xval : forall regs extra j n v, n = (32 + j)%nat -> nth j extra (Z_to_bv 64 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
bv_unsigned (ew (Ereg regs extra) n) = v.
Proof. intros regs extra j n v -> H Hv. rewrite ew_Ereg_extra, H. apply unsigned_lit_small. exact Hv. Qed.
Lemma c9b_af : forall E n v lo hi al, bv_unsigned (ew E n) = v -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E n (mkAF lo hi al).
Proof. intros E n v lo hi al H Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H. auto. Qed.

(* a register of a run's last state, as its symbolic value *)
Ltac c9b_reg HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
  lazymatch type of HS with st_ok ?segs ?E ?ssf (restrict ?H ms) =>
    rewrite (st_ok_restrict_reg segs H E ssf ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssf) r) in
    replace (sr_get (ss_regs ssf) r) with e by (vm_compute; reflexivity)
  end end.

(* the bytes a chunk holds *)
Lemma c9b_czero : forall E H mem b off n, YP09.chunk_ok rsegs E (mrestrict H mem) b (YP09.mkChunk off (CZero n)) ->
0 <= n -> rm_bytes rsegs H mem (b + off) (zeros (Z.to_nat n)).
Proof.
intros E H mem b off n Hc Hn. apply rm_bytes_aview. intros i Hi. unfold zeros in Hi |- *.
rewrite repeat_length in Hi. rewrite rm_nth_repeat by exact Hi.
destruct (Hc (Z.of_nat i) ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-.
unfold aview. rewrite Hb2. reflexivity.
Qed.
Lemma c9b_cval4 : forall E H mem b off e v, YP09.chunk_ok rsegs E (mrestrict H mem) b (YP09.mkChunk off (CVal 4 e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> rm_bytes rsegs H mem (b + off) (le32 v).
Proof.
intros E H mem b off e v Hc He Hv. unfold le32. apply rm_bytes_of_val.
exact (val_of_chunk_ok rsegs E _ b off 4 e v Hc He ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)).
Qed.
Lemma c9b_app : forall H mem a l1 a' l2, a' = a + Z.of_nat (length l1) ->
rm_bytes rsegs H mem a l1 -> rm_bytes rsegs H mem a' l2 -> rm_bytes rsegs H mem a (l1 ++ l2).
Proof. intros H mem a l1 a' l2 -> H1 H2. apply rm_bytes_app. split; assumption. Qed.

(* the shadow byte of an application address, and the shadow hull of a range, lie in the shadow band: outside
   every frame (in_app) *)
Lemma c9b_sh_out : forall F x, in_app F 1024 -> 0 <= x < kHighMemEnd ->
0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ (F <= shadow_of_addr SHADOW_OFF x < F + 1024).
Proof.
intros F x HF Hx. pose proof (rm_shadow_band x Hx) as Hb.
split; [unfold kLowMemEnd, kHighMemBeg in Hb; lia | exact (rm_shadow_not_app x F 1024 Hx HF)].
Qed.
Lemma c9b_hull_out : forall F x n s, in_app F 1024 -> 0 <= x -> x + n <= kHighMemEnd -> 0 < n ->
shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 64 /\ ~ (F <= s < F + 1024).
Proof.
intros F x n s HF Hx Hxn Hn Hs. unfold shadow_addr in Hs.
assert (D1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (D2 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia | unfold kHighMemEnd in Hxn; lia]).
assert (D3 : SHADOW_OFF + x / 8 - 8 < (SHADOW_OFF + x / 8) / 8 * 8).
{ pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)). lia. }
assert (D4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (x + n - 1) / 8).
{ pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)). lia. }
pose proof alloc_ceiling_val as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6BB_MEMCPY.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* a post with fewer registers and bytes changed is a post with more *)
Lemma c9b_post_weak : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob' (Wr Wr' : Z -> Prop)
  (Rr : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) W2 c2,
(forall r, In r clob -> In r clob') -> (forall a, Wr a -> Wr' a) ->
rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr Rr W2 c2 ->
rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob' Wr' Rr W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob' Wr Wr' Rr W2 c2 Hc HW
  (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ & Hr & Hf & Hp & Hio & Hmo & Hm & HR).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ|].
split; [intros r Hr0 Hn; apply Hr; [exact Hr0 | intros X; exact (Hn (Hc r X))]|].
split; [exact Hf|]. split; [exact Hp|]. split; [exact Hio|]. split; [exact Hmo|].
split; [intros a Ha Hn; apply Hm; [exact Ha | intros X; exact (Hn (HW a X))] | exact HR].
Qed.

(* ======================================== c9b_head: 0x812d4 .. the entry of checked_memcpy ======================================== *)
Definition c9b_R1 (W : world rsegs) (memc : word -> option byte) (R F : Z)
  : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W1 regs1 mem1 => W1 = W /\
getr regs1 2 = w64 R /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\ getr regs1 1 = w64 C9B_RET /\
getr regs1 10 = w64 (F + 0x220) /\ getr regs1 11 = w64 W6BB_S /\ getr regs1 12 = w64 14 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ c9b_e16 F a -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) /\
rm_bytes rsegs (w_H W1) mem1 (F + 0x210) c9b_L1.

Lemma c9b_head : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos c pp kd
  (r : list byte),
w6bb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6bb_in B W memc regs R F c pp kd r ->
SRr rsegs W (cfg_at rsegs W6BB_D9 regs memc mdc)
(rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6BB_MEMCPY [1; 10; 11; 12]%bv
  (c9b_e16 F) (c9b_R1 W memc R F)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp kd r Hctx Hin.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H27 & H19 & H18 & H16 & H22 & H6 & H20 & H13 & V48 & Vf0 & V110 & V130 & V140 &
  V158 & Hkd & Hpp & Hpp2 & HF4 & HFc & HF32 & HFapp & Hz & Hrae & Hhe & Hc1 & Hinp).
clear H27 H19 H18 H16 H22 H6 H20 H13 Vf0 V130 V140 Hkd Hpp Hpp2 Hrae Hhe Hc1 Hinp.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & HFpres & _).
rewrite <- HFa in HFpres. change (fs_frame_bytes 4) with 1024 in HFpres.
pose proof alloc_ceiling_val as (Hac & _).
unfold T_SEG_STK, ASTACK in HspR.
assert (HRb : 4096 <= R /\ R + 0x200 <= 2 ^ 47 /\ F + 1024 <= R) by lia.
destruct HRb as (HR0 & HR1 & HFR).
clear Hal HSTK0 Hceil Hlo Hhi H47 Hac HspR HRsp.
assert (B9 : bv_unsigned (ew (Ereg regs (c9b_extra1 F)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (B32 : bv_unsigned (ew (Ereg regs (c9b_extra1 F)) 32) = F + 0x210)
  by (apply (c9b_xval regs (c9b_extra1 F) 0 32 (F + 0x210) eq_refl eq_refl); lia).
assert (B33 : bv_unsigned (ew (Ereg regs (c9b_extra1 F)) 33) = F + 0x220)
  by (apply (c9b_xval regs (c9b_extra1 F) 1 33 (F + 0x220) eq_refl eq_refl); lia).
assert (B34 : bv_unsigned (ew (Ereg regs (c9b_extra1 F)) 34) = F + 0x218)
  by (apply (c9b_xval regs (c9b_extra1 F) 2 34 (F + 0x218) eq_refl eq_refl); lia).
assert (HS : st_ok rsegs (Ereg regs (c9b_extra1 F)) c9b_ss1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6BB_D9) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold c9b_rR. apply (rm_ro_region rsegs _ _ _ 9%nat R); [exact B9 | lia | lia |].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val rsegs _ _ R 0x48 8 (SOff 33 0) (F + 0x220));
          [exact (c9b_xatom regs (c9b_extra1 F) 1 33 eq_refl) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia | exact V48].
      * apply (chunk_ok_val rsegs _ _ R 0x110 8 (SOff 34 0) (F + 0x218));
          [exact (c9b_xatom regs (c9b_extra1 F) 2 34 eq_refl) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia | exact V110].
      * apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 32 0) (F + 0x210));
          [exact (c9b_xatom regs (c9b_extra1 F) 0 32 eq_refl) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia | exact V158].
    + unfold c9b_rE. apply (rm_rw_region rsegs _ _ _ 32%nat (F + 0x210)); [exact B32 | lia | lia | |].
      * intros o Ho. apply (proj1 (HFpres (F + 0x210 + o) ltac:(lia))).
      * constructor; [|constructor]. intros i Hi. cbn [YP09.c_len YP09.c_val YP09.cv_len] in Hi.
        exists (Z_to_bv 8 0). split; [reflexivity|]. cbn [YP09.c_off]. rewrite Z.add_0_r. apply Hz. lia.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c9b_rR, c9b_rE.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9, B32.
    split; [split; [right; lia | exact I] | split; exact I].
  - split; [|split; exact I]. unfold c9b_facts1. cbn [f_atoms atoms_ok].
    split; [apply (c9b_af _ _ R); [exact B9 | lia | | lia]|].
    { destruct (proj1 (Z.mod_divide R 16 ltac:(lia)) HR16) as [q ->]. change (2 ^ 4) with 16. apply Z_mod_mult. }
    split; [apply (c9b_af _ _ (F + 0x210)); [exact B32 | lia | change (2 ^ 4) with 16; apply c9b_mod16; [exact HF32 | reflexivity] | lia]|].
    split; [apply (c9b_af _ _ (F + 0x220)); [exact B33 | lia | change (2 ^ 4) with 16; apply c9b_mod16; [exact HF32 | reflexivity] | lia]|].
    split; [apply (c9b_af _ _ (F + 0x218)); [exact B34 | lia | change (2 ^ 3) with 8; apply c9b_mod8; [exact HF32 | reflexivity] | lia]|].
    exact I. }
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs. pose proof LAWS as HL.
unfold cfg_at. change (w64 W6BB_D9) with (Z_to_bv 64 W6BB_D9).
aj_run_to w6bb_tbl_ok HS HJ W6BB_MEMCPY.
{ (* the write rights: [R+0x48, R+0x160) is read-only, e62's window [0, 16) lies in the frame (4, pos) *)
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (rl_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0x210); [reflexivity | rewrite B32, HFa; reflexivity
  | exact Hown | cbn; lia | cbn; lia | apply awr_ok_nil]. }
(* at the entry of checked_memcpy *)
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ c9b_e16 F a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hrg & Hr). apply Hn. unfold c9b_e16. rewrite unsigned_lit_small in Hr by lia.
  unfold c9b_ss1 in Hrg. cbn [ss_mem In] in Hrg. destruct Hrg as [<-|[<-|[]]];
  unfold c9b_rR, c9b_rE in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B9, ?B32 in Hr; lia. }
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let r1 := eval vm_compute in (nth_error (ss_mem ssf) 1) in
  lazymatch r1 with Some ?rg =>
    assert (HRg : region_ok rsegs (Ereg regs (c9b_extra1 F)) (mrestrict (w_H W) (ms_mem ms)) rg)
      by (apply (rl_region_nth _ ssf ms 1 rg (w_H W) HS); vm_compute; reflexivity) end end.
pose proof (rl_chunks _ _ 32%nat (F + 0x210) _ _ _ _ _ HRg B32) as HC.
pose proof (HC (YP09.mkChunk 0 (CVal 4 (SLit 14))) ltac:(c9b_in)) as K0.
pose proof (HC (YP09.mkChunk 4 (CZero 4)) ltac:(c9b_in)) as K4.
pose proof (HC (YP09.mkChunk 8 (CVal 4 (SLit 14))) ltac:(c9b_in)) as K8.
pose proof (HC (YP09.mkChunk 12 (CVal 4 (SLit 8))) ltac:(c9b_in)) as K12.
pose proof (HC (YP09.mkChunk 16 (CZero 88)) ltac:(c9b_in)) as K16.
assert (Ca : rm_bytes rsegs (w_H W) (ms_mem ms) (F + 0x210 + 0) (le32 14))
  by exact (c9b_cval4 _ _ _ _ _ (SLit 14) 14 K0 eq_refl ltac:(lia)).
assert (Cb : rm_bytes rsegs (w_H W) (ms_mem ms) (F + 0x210 + 4) (zeros 4))
  by exact (c9b_czero _ _ _ _ _ 4 K4 ltac:(lia)).
assert (Cc : rm_bytes rsegs (w_H W) (ms_mem ms) (F + 0x210 + 8) (le32 14))
  by exact (c9b_cval4 _ _ _ _ _ (SLit 14) 14 K8 eq_refl ltac:(lia)).
assert (Cd : rm_bytes rsegs (w_H W) (ms_mem ms) (F + 0x210 + 12) (le32 8))
  by exact (c9b_cval4 _ _ _ _ _ (SLit 8) 8 K12 eq_refl ltac:(lia)).
assert (Ce : rm_bytes rsegs (w_H W) (ms_mem ms) (F + 0x210 + 16) (zeros 88))
  by exact (c9b_czero _ _ _ _ _ 88 K16 ltac:(lia)).
clear HC HRg K0 K4 K8 K12 K16.
lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ =>
  apply SRr_ret; exists lyc, Sc, (ms_regs ms), (ms_mem ms), md end.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (c9b_extra1 F) (w_H W) _ HS (env_agree_refl _ _));
  vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [c9b_kio|].
split; [apply mo_le_refl; exact MTL|].
split; [exact KE|].
split; [reflexivity|].
split; [c9b_reg HS; exact (eq_trans (c9b_atom regs _ 2 2%bv eq_refl) H2)|].
split; [c9b_reg HS; exact (eq_trans (c9b_atom regs _ 3 3%bv eq_refl) H3)|].
split; [c9b_reg HS; exact (eq_trans (c9b_atom regs _ 4 4%bv eq_refl) H4)|].
split; [c9b_reg HS; reflexivity|].
split; [c9b_reg HS; exact (c9b_xatom regs (c9b_extra1 F) 1 33 eq_refl)|].
split; [c9b_reg HS; reflexivity|].
split; [c9b_reg HS; reflexivity|].
split; [exact KE|].
rewrite Z.add_0_r in Ca. unfold c9b_L1.
apply (c9b_app _ _ _ _ (F + 0x210 + 4)); [rewrite length_le32; lia | exact Ca |].
apply (c9b_app _ _ _ _ (F + 0x210 + 8)); [rewrite length_zeros; lia | exact Cb |].
apply (c9b_app _ _ _ _ (F + 0x210 + 12)); [rewrite length_le32; lia | exact Cc |].
apply (c9b_app _ _ _ _ (F + 0x210 + 16)); [rewrite length_le32; lia | exact Cd | exact Ce].
Qed.

(* ======================================== c9b_tail: 0x81320 .. J ======================================== *)
Lemma c9b_tail : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos q p,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos -> F mod 32 = 0 ->
R mod 16 = 0 -> 4096 <= R -> R + 0x200 <= 2 ^ 47 -> F + 1024 <= R ->
getr regs 9 = w64 R ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 q -> 0 <= q < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 p -> 0 <= p < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 (F + 0x210) ->
SRr rsegs W (cfg_at rsegs C9B_RET regs memc mdc)
(rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6BB_J [6; 10; 11; 13; 15; 22]%bv
  (fun a => F + 0x214 <= a < F + 0x218)
  (fun W2 regs2 mem2 => getr regs2 22 = w64 q /\ getr regs2 15 = w64 p /\
     getr regs2 13 = getr regs 18 /\ getr regs2 6 = getr regs 22 /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x214) 4 24)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos q p HJ Hown HFa HF32 HR16 HR0 HR1 HFR
  H9 V130 Hq V140 Hp V158.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & HFpres & _).
rewrite <- HFa in HFpres. change (fs_frame_bytes 4) with 1024 in HFpres.
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & _).
rewrite <- HFa in HF4096.
assert (B9 : bv_unsigned (ew (Ereg regs (c9b_extra3 F q p)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (B32 : bv_unsigned (ew (Ereg regs (c9b_extra3 F q p)) 32) = F + 0x210)
  by (apply (c9b_xval regs (c9b_extra3 F q p) 0 32 (F + 0x210) eq_refl eq_refl); lia).
assert (HS : st_ok rsegs (Ereg regs (c9b_extra3 F q p)) c9b_ss3
  (restrict (w_H W) (mkst regs (Z_to_bv 64 C9B_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold c9b_rS. apply (rm_ro_region rsegs _ _ _ 9%nat R); [exact B9 | lia | lia |].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val rsegs _ _ R 0x130 8 (SOff 33 0) q);
          [exact (c9b_xatom regs (c9b_extra3 F q p) 1 33 eq_refl) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia | exact V130].
      * apply (chunk_ok_val rsegs _ _ R 0x140 8 (SOff 34 0) p);
          [exact (c9b_xatom regs (c9b_extra3 F q p) 2 34 eq_refl) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia | exact V140].
      * apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 32 0) (F + 0x210));
          [exact (c9b_xatom regs (c9b_extra3 F q p) 0 32 eq_refl) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia | exact V158].
    + unfold c9b_rZ. apply (rm_rw_region rsegs _ _ _ 32%nat (F + 0x210)); [exact B32 | lia | lia | | constructor].
      intros o Ho. apply (proj1 (HFpres (F + 0x210 + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c9b_rS, c9b_rZ.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9, B32.
    split; [split; [right; lia | exact I] | split; exact I].
  - split; [|split; exact I]. unfold c9b_facts3. cbn [f_atoms atoms_ok].
    split; [apply (c9b_af _ _ R); [exact B9 | lia | | lia]|].
    { destruct (proj1 (Z.mod_divide R 16 ltac:(lia)) HR16) as [q' ->]. change (2 ^ 4) with 16. apply Z_mod_mult. }
    split; [apply (c9b_af _ _ (F + 0x210)); [exact B32 | lia | change (2 ^ 4) with 16; apply c9b_mod16; [exact HF32 | reflexivity] | lia]|].
    exact I. }
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs. pose proof LAWS as HL.
unfold cfg_at. change (w64 C9B_RET) with (Z_to_bv 64 C9B_RET).
aj_run_to w6bb_tbl_ok HS HJ W6BB_J.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (rl_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0x210); [reflexivity | rewrite B32, HFa; reflexivity
  | exact Hown | cbn; lia | cbn; lia | apply awr_ok_nil]. }
(* at J *)
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let r1 := eval vm_compute in (nth_error (ss_mem ssf) 1) in
  lazymatch r1 with Some ?rg =>
    assert (HR1' : region_ok rsegs (Ereg regs (c9b_extra3 F q p)) (mrestrict (w_H W) (ms_mem ms)) rg)
      by (apply (rl_region_nth _ ssf ms 1 rg (w_H W) HS); vm_compute; reflexivity) end end.
pose proof (rl_chunks _ _ 32%nat (F + 0x210) _ _ _ _ _ HR1' B32 (YP09.mkChunk 4 (CVal 4 (SLit 24)))
  ltac:(c9b_in)) as C4.
lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ =>
  apply SRr_ret; exists lyc, Sc, (ms_regs ms), (ms_mem ms), md end.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (c9b_extra3 F q p) (w_H W) _ HS (env_agree_refl _ _));
  vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [c9b_kio|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hrg & Hr). apply Hn. cbv beta. rewrite unsigned_lit_small in Hr by lia.
  unfold c9b_ss3 in Hrg. cbn [ss_mem In] in Hrg. destruct Hrg as [<-|[<-|[]]];
  unfold c9b_rS, c9b_rZ in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B9, ?B32 in Hr; lia. }
split; [c9b_reg HS; exact (c9b_xatom regs (c9b_extra3 F q p) 1 33 eq_refl)|].
split; [c9b_reg HS; exact (c9b_xatom regs (c9b_extra3 F q p) 2 34 eq_refl)|].
split; [c9b_reg HS; exact (c9b_atom regs _ 18 18%bv eq_refl)|].
split; [c9b_reg HS; exact (c9b_atom regs _ 22 22%bv eq_refl)|].
replace (F + 0x214) with (F + 0x210 + 4) by lia.
exact (val_of_chunk_ok rsegs _ _ (F + 0x210) 4 4 (SLit 24) 24 C4 eq_refl ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia)
  ltac:(cbn; lia)).
Qed.

(* ======================================== the block lemma ======================================== *)
Theorem w6bb_c9 : w6bb_c9_stmt B MT.
Proof using MTL AMEMCPY.
unfold w6bb_c9_stmt, w6bb_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b r Hctx Hkd Hin Hs.
pose proof Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & Hrom).
pose proof Hin as (H2 & H3 & H4 & H9 & H27 & H19 & H18 & H16 & H22 & H6 & H20 & H13 & V48 & Vf0 & V110 & V130 & V140 &
  V158 & Hkdr & Hpp & Hpp2 & HF4 & HFc & HF32 & HFapp & Hz & Hrae & Hhe & Hc1 & Hinp).
clear H27 H19 H16 H6 H20 H13 V48 Vf0 V110 Hkdr Hz Hc1 Hinp.
pose proof HJ as (HAR & HLc & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof alloc_ceiling_val as (Hac & _).
unfold T_SEG_STK, ASTACK in HspR.
assert (HRb : 4096 <= R /\ R + 0x200 <= 2 ^ 47 /\ F + 1024 <= R /\ alloc_ceiling + 16384 <= R) by lia.
destruct HRb as (HR0 & HR1 & HFR & HRc).
(* the source: ent_build.s, 13 bytes and the NUL, in the image *)
destruct Hs as (Hsb & Hsn & _ & _ & _ & Hsimg & _ & Hsra & Hshl).
assert (LS : Z.of_nat (length (map (fun x : byte => bv_unsigned x) S9)) = 13) by (vm_compute; reflexivity).
rewrite LS in Hsb, Hsn, Hsimg, Hsra, Hshl.
(* no byte of the image lies in the frame (4, pos) *)
assert (Himg : forall a, W6BB_S <= a < W6BB_S + 14 -> ~ (F <= a < F + 1024)).
{ intros a Ha Hf.
  assert (HinF : frame_addr lyc 4 pos <= a < frame_addr lyc 4 pos + fs_frame_bytes 4)
    by (rewrite <- HFa; change (fs_frame_bytes 4) with 1024; lia).
  destruct (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR
    (or_intror (or_introl (ex_intro _ 4 (ex_intro _ pos (conj Hin4 HinF)))))) as [_ Hni].
  apply Hni. replace a with (W6BB_S + (a - W6BB_S)) by lia. apply Hsimg. unfold W6BB_S in *. lia. }
(* the source's 14 bytes at the entry *)
assert (HsB : rm_bytes rsegs (w_H W) memc W6BB_S (S9 ++ [NUL])).
{ apply rm_bytes_aview. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  assert (L9 : length S9 = 13%nat) by (vm_compute; reflexivity). rewrite L9 in Hi.
  destruct (Nat.lt_ge_cases i 13) as [Hl|Hg].
  - rewrite app_nth1 by (rewrite L9; exact Hl).
    rewrite (Hsb (Z.of_nat i) ltac:(lia)), Nat2Z.id, rm_nth_map. reflexivity.
  - assert (i = 13%nat) by lia. subst i. rewrite app_nth2 by (rewrite L9; lia). rewrite L9, Nat.sub_diag.
    cbn [nth]. exact Hsn. }
pose proof (rl_fbounds F HF32 HFapp) as (_ & _ & _ & _ & _ & Hamr).
eapply SRr_mono.
{ eapply (rl_wpost_seq B MT MTL) with (R2 := w6bb_J_R R F c pp r (b :: r)) (clob2 := [6; 10; 11; 13; 15; 22]%bv)
    (Wr2 := fun a => F + 0x214 <= a < F + 0x218).
  - eapply (rl_intrin_seq B MT LAWS OCpy W6BB_MEMCPY C9B_RET AMEMCPY) with (d := F + 0x220) (x := W6BB_S) (n := 14)
      (o := R - sp0).
    + exact (c9b_head STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp (bv_unsigned b) r Hctx Hin).
    + (* the call's premises at the entry of checked_memcpy *)
      intros ly1 S1 W1 regs1 mem1 md1 HJ1 (-> & G2 & G3 & G4 & G1 & G10 & G11 & G12 & GK & GB).
      pose proof HJ1 as (_ & HL1 & _).
      assert (HF1 : frame_addr ly1 4 pos = F) by (rewrite HFa; exact (c9b_faddr _ _ _ _ _ 4 pos HL1 HLc)).
      assert (Hsp1 : spZ regs1 = R) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
      (* a byte outside e62's first 16 bytes is kept by the head *)
      assert (Ksh : forall x, 0 <= x < kHighMemEnd ->
        aview rsegs (w_H W) mem1 (shadow_of_addr SHADOW_OFF x) = aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
      { intros x Hx. destruct (c9b_sh_out F x HFapp Hx) as [Hs1 Hs2]. apply GK; [exact Hs1|]. unfold c9b_e16. lia. }
      assert (Khl : forall x n, 0 <= x -> x + n <= kHighMemEnd -> 0 < n ->
        shadow_hull_vis (aview rsegs (w_H W) memc) x n -> shadow_hull_vis (aview rsegs (w_H W) mem1) x n).
      { intros x n Hx Hxn Hn Hh. apply (rm_hull_kept rsegs (w_H W) memc (w_H W) mem1 x n Hh).
        intros s Hs Hnn. destruct (c9b_hull_out F x n s HFapp Hx Hxn Hn Hs) as [Hs1 Hs2].
        rewrite GK; [exact Hnn | exact Hs1 | unfold c9b_e16; lia]. }
      assert (Kimg : forall a, W6BB_S <= a < W6BB_S + 14 -> aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a).
      { intros a Ha. pose proof (Himg a Ha). apply GK; [unfold W6BB_S in *; lia | unfold c9b_e16; lia]. }
      split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
      split; [rewrite Hsp1; lia|].
      split; [exact G3|]. split; [exact G4|]. split; [exact G1|].
      split.
      { intros a Ha. split.
        - apply (rl_awr_fobj STK sp0 FP _ _ ly1 own pos a Hown). rewrite HF1. lia.
        - unfold ESTACK. lia. }
      split.
      { apply (rm_ra_kept rsegs (w_H W) memc (w_H W) mem1 SHADOW_OFF (F + 0x220) 14).
        - eapply ra_sub; [exact Hrae | lia | lia].
        - intros x Hx. apply Ksh. unfold kHighMemEnd. lia. }
      split.
      { intros _. apply Khl; [lia | unfold kHighMemEnd; lia | lia |].
        apply (rm_hull_sub _ (F + 0x210) 104); [exact Hhe | lia | lia | lia]. }
      cbv iota. split; [unfold W6BB_S; lia|]. split; [unfold W6BB_S; lia|].
      split.
      { intros a Ha. rewrite Hsp1. split.
        - rewrite (Kimg a Ha). replace a with (W6BB_S + (a - W6BB_S)) by lia.
          destruct (Z.eq_dec (a - W6BB_S) 13) as [E13|N13]; [rewrite E13, Hsn; discriminate|].
          rewrite (Hsb (a - W6BB_S) ltac:(lia)). discriminate.
        - unfold ESTACK, W6BB_S in *. lia. }
      split.
      { destruct (Z_le_gt_dec (F + 0x220 + 14) W6BB_S) as [X|X]; [left; exact X|].
        destruct (Z_le_gt_dec (W6BB_S + 14) (F + 0x220)) as [Y|Y]; [right; exact Y|].
        exfalso. apply (Himg (Z.max W6BB_S (F + 0x220)) ltac:(lia)). lia. }
      split; [unfold amem_range, W6BB_S, kLowMemEnd; left; lia|].
      split.
      { apply (rm_ra_kept rsegs (w_H W) memc (w_H W) mem1 SHADOW_OFF W6BB_S 14); [exact Hsra|].
        intros x Hx. apply Ksh. unfold kHighMemEnd, W6BB_S in *. lia. }
      intros _. apply Khl; [unfold W6BB_S; lia | unfold kHighMemEnd, W6BB_S; lia | lia | exact Hshl].
    + lia.
    + lia.
    + lia.
    + apply Hamr; lia.
    + rewrite Zminus_mod, HR16, Hal. reflexivity.
    + lia.
    + unfold ESTACK. lia.
    + exact c9b_ret_ok.
  - (* 0x81320 .. J *)
    intros W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HRq.
    destruct HRq as (regsB & memB & HRB & Hcs & H10' & Hcpy & Hkc).
    destruct HRB as (-> & G2 & G3 & G4 & G1 & G10 & G11 & G12 & GK & GB).
    pose proof HJ1 as (_ & HL1 & _).
    assert (HF1 : F = frame_addr ly1 4 pos) by (rewrite HFa; symmetry; exact (c9b_faddr _ _ _ _ _ 4 pos HL1 HLc)).
    assert (E9 : getr regs1 9 = w64 R).
    { rewrite Hr1; [exact H9 | apply c9b_nz; reflexivity | apply c9b_notin; reflexivity]. }
    assert (E18 : getr regs1 18 = getr regs 18).
    { rewrite Hr1; [reflexivity | apply c9b_nz; reflexivity | apply c9b_notin; reflexivity]. }
    assert (E22 : getr regs1 22 = getr regs 22).
    { rewrite Hr1; [reflexivity | apply c9b_nz; reflexivity | apply c9b_notin; reflexivity]. }
    assert (V130' : val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x130) 8 (pp + 0x4000)).
    { apply (rl_val_kept (w_H W) memc mem1); [|exact V130].
      intros j Hj. rewrite (Hm1 (R + 0x130 + j) ltac:(lia)); [reflexivity|].
      intros X. cbv beta in X. unfold c9b_e16, ESTACK in X. lia. }
    assert (V140' : val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x140) 8 pp).
    { apply (rl_val_kept (w_H W) memc mem1); [|exact V140].
      intros j Hj. rewrite (Hm1 (R + 0x140 + j) ltac:(lia)); [reflexivity|].
      intros X. cbv beta in X. unfold c9b_e16, ESTACK in X. lia. }
    assert (V158' : val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x158) 8 (F + 0x210)).
    { apply (rl_val_kept (w_H W) memc mem1); [|exact V158].
      intros j Hj. rewrite (Hm1 (R + 0x158 + j) ltac:(lia)); [reflexivity|].
      intros X. cbv beta in X. unfold c9b_e16, ESTACK in X. lia. }
    assert (L14 : length (S9 ++ [NUL]) = 14%nat) by (vm_compute; reflexivity).
    assert (L104 : length c9b_L1 = 104%nat) by (vm_compute; reflexivity).
    assert (HL2 : rm_bytes rsegs (w_H W) mem1 (F + 0x210) c9b_L2).
    { unfold c9b_L2. apply (rm_bytes_patch rsegs (w_H W) memB (w_H W) mem1 (F + 0x210) c9b_L1 16 (S9 ++ [NUL]) GB).
      - apply (rm_memcpy_bytes rsegs (w_H W) memB (w_H W) mem1 W6BB_S).
        + apply (rm_bytes_kept rsegs (w_H W) memc (w_H W) memB W6BB_S _ HsB).
          intros x Hx. rewrite L14 in Hx.
          pose proof (Himg x Hx). apply GK; [unfold W6BB_S in *; lia | unfold c9b_e16; lia].
        + intros i Hi. rewrite L14 in Hi.
          replace (F + 0x210 + Z.of_nat 16 + i) with (F + 0x220 + i) by lia. exact (Hcpy i Hi).
      - rewrite L14, L104. lia.
      - intros y Hy Hny. rewrite L104 in Hy. rewrite L14 in Hny. apply Hkc; [lia | lia | unfold ESTACK; lia]. }
    eapply SRr_mono.
    { apply (c9b_tail STK sp0 FP ly S W0 mem0 md0 own k ly1 S1 W mem1 md1 regs1 R F pos (pp + 0x4000) pp HJ1 Hown HF1
        HF32 HR16 HR0 HR1 HFR E9 V130' ltac:(lia) V140' ltac:(lia) V158'). }
    intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 &
      (T22 & T15 & T13 & T6 & T4)).
    exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ2|].
    split; [exact Hr2|]. split; [exact Hf2|]. split; [exact Hp2|]. split; [exact Hio2|]. split; [exact Hmo2|].
    split; [exact Hm2|].
    unfold w6bb_J_R. rewrite (c9b_ent_build b r Hkd). cbn [fst snd].
    split; [exact T22|].
    split; [exact T15|].
    split; [rewrite T13, E18, H18; f_equal; lia|].
    split; [rewrite T6, E22, H22; reflexivity|].
    rewrite c9b_ent_mem.
    change (rm_bytes rsegs (w_H W2) mem2 (F + 0x210) (Model.overwrite c9b_L2 4 (le32 24))).
    assert (L2l : length c9b_L2 = 104%nat) by (vm_compute; reflexivity).
    unfold le32. apply (rm_bytes_store rsegs (w_H W) mem1 (w_H W2) mem2 (F + 0x210) c9b_L2 4 4 24 HL2).
    + replace (F + 0x210 + Z.of_nat 4) with (F + 0x214) by lia. exact T4.
    + rewrite L2l. lia.
    + intros y Hy Hny. rewrite L2l in Hy. apply Hm2; [lia | cbv beta; lia]. }
intros W2 c2 _ Hpost.
refine (c9b_post_weak _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpost).
- apply c9b_incl. vm_compute. reflexivity.
- intros a Ha. cbv beta in Ha. unfold w6bb_wr, T_SEG_STK, ASTACK. unfold c9b_e16, ESTACK in Ha. lia.
Qed.

End d.
End b.
