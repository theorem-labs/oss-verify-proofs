(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address below is measured on its unstripped
   twin sha256 6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): one turn of the property loop of
   LLVMFuzzerTestOneInput (0x7ff88) outside the params Struct, piece by piece. Proves no function (kind: segment
   lemma): each lemma is a block of the entry function, from a fixed pc to one of its exits.

   THE BLOCKS (pod.h:397-412, the inlined pod_build loop `for (i = 0; i < nprops; i++)`)
     0x805e8 N       sd a6,0xb8(s1); the sel byte (fuzz_u8 at the cursor R+0xc8 / R+0xf8, its shadow check
                     0x80600 of the EQ-J form `lb; beqz t,+8; j 0x81d84`); pp->len's shadow check 0x80630;
                     a0 = len, a2 = len - 0x3ffd; `bne sh,7` 0x80650 -> 0x80654 (sh = 7) / 0x80800.
     0x80654 SEL7    a Struct's Int pod: put32 4 (size), put32 4 (type), 4 zero body bytes, the pad memset 0x807dc
                     (4 bytes), a6 = i; `j 0x81d74`.
     0x80800 SELK    the key put32 (0x80001 when sel mod 4 <> 0, else 0x10003), the flags put32 0, seen' (R+0x88),
                     first (R+0xd0), at (R+0xa0); `bnez` 0x80938 -> 0x80940 (params Struct) / 0x81ae8 (Int 7).
     0x81d6c LATCH   a6 = i (R+0xb8), s9 = seen' (R+0x88); 0x81d74 LATCH7: a6 = i + 1, `beq a6,np` -> 0x81ed8 (P1)
                     else `j 0x805e8` (N).
   Each block is stated in the shape of a callee contract (lib/A/RPgSteps.v rl_blk_post: the journal without an
   event, every register outside clob kept, frames / blocks / I/O / meter kept), with the bytes it may write named by
   a set Ew and what it computes by a relation over the end world, registers and memory. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the pcs ---- *)
Definition PA_N : Z := 0x805e8.
Definition PA_SEL7 : Z := 0x80654.
Definition PA_SELK : Z := 0x80800.
Definition PA_SELS : Z := 0x80940.
Definition PA_SELI : Z := 0x81ae8.
Definition PA_LATCH : Z := 0x81d6c.
Definition PA_LATCH7 : Z := 0x81d74.
Definition PA_P1 : Z := 0x81ed8.
(* the 1544 instruction words 0x805e8 .. 0x81e04: the four blocks and their out-of-line slow paths 0x81d84 .. 0x81e04 *)
Definition pa_tbl : ctable := build_table rsegs PA_N 1544 TEmpty.
Lemma pa_tbl_ok : table_ok rsegs pa_tbl.
Proof. apply build_table_ok0. unfold PA_N. lia. Qed.
Lemma pa_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma pa_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* ---- the walk's context: env slot 32 is the shadow offset K; slots 33.. the block's own quantities ---- *)
Definition PABx : sv := SOff 32 0.
Definition PAspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pa_extra (l : list Z) : list word := Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) l.
Lemma pa_extra_K : forall regs l, ew (Ereg regs (pa_extra l)) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros. reflexivity. Qed.

Section k. Context {fx : YK11.FPState}.
(* an 8-byte chunk from the cell's value *)
Lemma pa_chunk8 : forall E m base off v val,
sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> val_mem rsegs m (base + off) 8 val ->
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 v)).
Proof.
intros E m base off v val Hv Hval Hw i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len cbyte] in Hi |- *.
exists (byte_of_word (sv_denot E v) i). split; [reflexivity|].
replace (base + off + i) with (base + off + Z.of_nat (Z.to_nat i)) by lia. rewrite (Hw (Z.to_nat i)) by lia.
f_equal. unfold byte_of_word, YO0f.le_byte. rewrite Hv, Z2Nat.id by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small val (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End k.


(* ---- the walk's plumbing [lib/A/RPgCfgChanges.v cfg_keep / cfg_kwr_ro, lib/A/RPgSteps.v rl_jt_block's leaf] ---- *)
(* KE : every byte outside the zone Zn as at the block's start; a run whose write windows lie in Zn keeps it *)
Ltac pa_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (RPgCfgChanges.kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the write windows of a state without one *)
Ltac pa_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
Ltac pa_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok pa_tbl_ok HS HJ SHOK PAspan stop; [awr_ok_tac | ] end.
Ltac pa_runb :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok pa_tbl_ok HS HJ SHOK PAspan; [awr_ok_tac | ] end.
Ltac pa_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok pa_tbl_ok HS SH PAspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* the value of register r at the end of a run, as the symbolic state holds it *)
Ltac pa_reg r :=
lazymatch goal with HS : st_ok ?sg ?E ?ssf (restrict ?H ?ms) |- context [getr (ms_regs ?ms) r] =>
rewrite (st_ok_restrict_reg sg H E ssf ms r HS);
let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* the leaf: the post's first eight clauses; the relation is left *)
Ltac pa_leaf extra :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  HAE : env_agree 32 (Ereg ?regs _) ?E, KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
apply SRr_ret;
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
split; [exact HJ|];
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs extra (w_H W) _ HS HAE); vm_compute; reflexivity|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz; exact (KE a Ha Hz)|]
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the post of a block: lib/A/RPgSteps.v rl_blk_post with the bytes Ew it may write and a relation R over the end
   world, registers and memory *)
Definition pa_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (pc : Z)
(clob : list (bv 5)) (Ew : Z -> Prop) (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world rsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (w64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\
frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Ew a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
R W2 regs2 mem2.

End d.
End b.
