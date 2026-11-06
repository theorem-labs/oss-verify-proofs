(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pp_cuts.v (a working branch e2e59892bef),
   re-walked for B's code (B-readings.lst 0x82060 .. 0x821c0): A's segment structure, B's registers, loop layout and
   UBSan guards. *)
(* lv2_locate_manifest_readings on fm.asan-ubsan, segment PP (rd_seg_P of lib/B/FMW_rd_cuts.v): the shared base of the
   declaration body's walk from P (0x82060) to the strchr call (0x821bc) -- the symbolic states and entry lemmas of its
   cut points, the byte classifications of its branches, and the invariants at its inner cuts:
     L1  0x82098  while (isspace (p[0])) p++          lv2_locate.c:116  (a1 = s6 = p0 + k, a0 = p0 + k + 1)
     L2  0x820ec  while (name_ok (p[m])) m++          lv2_locate.c:120  (a2 = the byte at s8 = p1 + m, a1 = -m)
     L3E 0x82150  the name ended with ':' at s8 = p2: the guard on s8, F+0x48 := m = p2 - p1
     L3  0x8215c  while (isspace (q[1])) q++          lv2_locate.c:126  (s8 = p2 + j, the byte loaded at s8 + 1)
     ST  0x821ac  the '<' at a0 = p3: the guard on a0, s8 := p3 + 1 = ns, strchr (ns, '>')
   B keeps -1 in s0, 32 in s2, 5 in s3, RD_MASK1 in s4, 58 in s7 (rd_loop), at in s5 and the shadow base in s11; s9 and
   s10 count down from u - 2 - s11 - at and u - 2 - p0, once per byte consumed after p0, in all three loops.
   Every UBSan guard (a branch to RD_TRAP 0x823b4) of the stretch is refuted where it is reached: 0x820b4 (s6),
   0x82104 (s8), 0x82150 (s8), 0x82188/0x8218c (a0, the third loop's back edge), 0x821ac (a0), and CONT's 0x8200c/0x82010
   (a0 = s5 = at): each tested pointer is a text position below alloc_ceiling, never -1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the pcs of this segment ---- *)
Definition PP_SP : Z := 0x82080.   (* the space body: a1 = p0, s9, s10, a0 = p0 + 1      lv2_locate.c:116 *)
Definition PP_L1 : Z := 0x82098.   (* while (isspace (p[0])) p++                          lv2_locate.c:116 *)
Definition PP_L2 : Z := 0x820ec.   (* while (name_ok (p[m])) m++                          lv2_locate.c:120 *)
Definition PP_L3E : Z := 0x82150.  (* the ':' at p2: guard, F+0x48 := p2 - p1             lv2_locate.c:121-125 *)
Definition PP_L3 : Z := 0x8215c.   (* while (isspace (q[1])) q++                          lv2_locate.c:126 *)
Definition PP_ST : Z := 0x821ac.   (* the '<' at p3: guard, ns = p3 + 1, strchr (ns, '>') lv2_locate.c:127-129 *)
Definition PP_RA : Z := 0x821c0.   (* = RD_C8, the return address of strchr *)

(* ---- the shadow-token setup: s11 (register 27) holds the shadow base ---- *)
Definition PP_Bx : sv := SOff 27 0.
Definition PP_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* ---- the registers: rd_loop's constants pinned (s0 = -1, s2 = 32, s3 = 5, s4 = RD_MASK1, s7 = 58), the rest atoms ---- *)
Definition pp_regs0 : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 8%bv (SLit RD_M1)) 18%bv (SLit 32)) 19%bv (SLit 5))
    20%bv (SLit RD_MASK1)) 23%bv (SLit 58).

(* ---- the regions: atoms 32 = u - 2 (slot 0x58), 33 = the byte the walk loads, 34 = p0 = at + s11 (the alias) ---- *)
Definition pp_frameR : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x58 0x60 0x58 0x58 [YP09.mkChunk 0x58 (CVal 8 (SOff 32 0))].
Definition pp_sc48 : YP09.region := YP09.mkRegion (Some 2%nat) 0x48 0x50 0x48 0x50 [].
Definition pp_byte (n : nat) (off : Z) : YP09.region :=
  YP09.mkRegion (Some n) off (off + 1) off off [YP09.mkChunk off (CVal 1 (SOff 33 0))].

Definition PP_AF2 : nat * afact := (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4).
Definition PP_AF27 : nat * afact := (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
Definition pp_afstr (n : nat) : nat * afact := (n, mkAF 4096 (2 ^ 47 - 16) 0).
Definition pp_afbyte (n : nat) : nat * afact := (n, mkAF 0 255 0).

(* ---- P 0x82060 and the space body 0x82080: a0 = s11 (atom 10), s5 = at (atom 21); at + s11 is atom 34 ---- *)
Definition ss_pp_Pat (pc : Z) : sstate :=
  mkSS pc pp_regs0 [pp_frameR; pp_byte 34 0] None
    (mkFacts [PP_AF2; PP_AF27; pp_afstr 34; pp_afbyte 33] []
       [(SAlu ALU_ADD (SOff 21 0) (SOff 10 0), SOff 34 0); (SAlu ALU_ADD (SOff 10 0) (SOff 21 0), SOff 34 0)]).
Definition ss_pp_P : sstate := ss_pp_Pat RD_P.
Definition ss_pp_SP : sstate := ss_pp_Pat PP_SP.

(* ---- L1 0x82098: a1 = s6 = p0 + k (atoms 11, 22), the byte at s6 ---- *)
Definition ss_pp_L1 : sstate :=
  mkSS PP_L1 pp_regs0 [pp_byte 22 0] None (mkFacts [PP_AF2; PP_AF27; pp_afstr 11; pp_afstr 22; pp_afbyte 33] [] []).

(* ---- L2 0x820ec: a2 = the byte at s8 = p1 + m (atoms 12, 24), a0 = p1 + m + 1 (atom 10, the checked address of the
   next byte), the next byte at s8 + 1; the exit case's state has no next byte ---- *)
Definition ss_pp_L2 : sstate :=
  mkSS PP_L2 pp_regs0 [pp_byte 24 1] None
    (mkFacts [PP_AF2; PP_AF27; pp_afbyte 12; pp_afstr 10; pp_afstr 24; pp_afbyte 33] [] []).
Definition ss_pp_L2x : sstate :=
  mkSS PP_L2 pp_regs0 [] None (mkFacts [PP_AF2; PP_AF27; pp_afbyte 12; pp_afstr 10; pp_afstr 24] [] []).

(* ---- L3E 0x82150: s8 = p2 (atom 24), the slot F+0x48 writable ---- *)
Definition ss_pp_L3E : sstate :=
  mkSS PP_L3E pp_regs0 [pp_sc48] None (mkFacts [PP_AF2; PP_AF27; pp_afstr 24] [] []).

(* ---- L3 0x8215c: s8 = p2 + j (atom 24), the byte at s8 + 1 ---- *)
Definition ss_pp_L3 : sstate :=
  mkSS PP_L3 pp_regs0 [pp_byte 24 1] None (mkFacts [PP_AF2; PP_AF27; pp_afstr 24; pp_afbyte 33] [] []).

(* ---- ST 0x821ac: a0 = p3 (atom 10); no memory access before the call ---- *)
Definition ss_pp_ST : sstate := mkSS PP_ST pp_regs0 [] None (mkFacts [PP_AF2; PP_AF27; pp_afstr 10] [] []).

(* ---- pure model: the three loops count a prefix of a byte class ---- *)
Lemma pp_nth_skipn : forall k (l : list Z) j d, nth j (skipn k l) d = nth (k + j) l d.
Proof.
induction k as [|k IH]; intros l j d; [reflexivity|].
destruct l as [|x l]; cbn; [destruct j; reflexivity | apply IH].
Qed.

Lemma pp_cw_shift : forall f l p k, (k <= count_while f (skipn p l))%nat ->
  count_while f (skipn p l) = (k + count_while f (skipn (p + k) l))%nat.
Proof.
intros f l p k. revert p. induction k as [|k IH]; intros p Hk.
- rewrite Nat.add_0_r. reflexivity.
- assert (Hp : (p < length l)%nat).
  { destruct (Nat.lt_ge_cases p (length l)) as [H|H]; [exact H|].
    rewrite readings_scan.cw_end in Hk by lia. lia. }
  rewrite (readings_scan.cw_step f l p Hp) in Hk |- *.
  destruct (f (byte_at l p)) eqn:Hf; [|lia].
  replace (p + S k)%nat with (S p + k)%nat by lia.
  rewrite (IH (S p) ltac:(lia)). lia.
Qed.

Lemma pp_cw_exact : forall f l p k, (k <= count_while f (skipn p l))%nat -> f (byte_at l (p + k)) = false ->
  count_while f (skipn p l) = k.
Proof.
intros f l p k Hk Hf. rewrite (pp_cw_shift f l p k Hk).
destruct (Nat.lt_ge_cases (p + k) (length l)) as [H|H].
- rewrite (readings_scan.cw_step f l (p + k) H), Hf. lia.
- rewrite readings_scan.cw_end by lia. lia.
Qed.

Lemma pp_cw_le : forall f l p, (count_while f (skipn p l) <= length l - p)%nat.
Proof.
intros f l p. pose proof (readings_scan.cw_le f (skipn p l)) as H. rewrite length_skipn in H. exact H.
Qed.

(* one more byte of the class consumed *)
Lemma pp_cw_next : forall f l p k, (k <= count_while f (skipn p l))%nat ->
  f (byte_at l (p + k)) = true -> (p + k < length l)%nat -> (S k <= count_while f (skipn p l))%nat.
Proof.
intros f l p k Hk Hf Hlt. rewrite (pp_cw_shift f l p k Hk), (readings_scan.cw_step f l (p + k) Hlt).
destruct (f (byte_at l (p + k))) eqn:Ef; [lia | congruence].
Qed.

(* a byte other than NUL is inside the text *)
Lemma pp_lt_of_nz : forall (tb : list Z) q, byte_at tb q <> 0 -> (q < length tb)%nat.
Proof.
intros tb q H. destruct (Nat.lt_ge_cases q (length tb)) as [Hq|Hq]; [exact Hq|].
exfalso. apply H. exact (readings_scan.byte_at_past tb q Hq).
Qed.

Lemma pp_sp_nz : forall c, is_space c = true -> c <> 0.
Proof. intros c H Hz. subst c. vm_compute in H. discriminate H. Qed.

Lemma pp_head_le : forall t i p, head t i = Some p -> (p <= length t)%nat.
Proof.
intros t i p H. unfold head in H.
destruct ((byte_at t i =? 64) && zl_eqb (firstn 6 (skipn (S i) t)) prefix_lc) eqn:E1.
- injection H as <-. apply andb_true_iff in E1 as [_ E1]. apply zl_eqb_eq in E1.
  assert (E : length (firstn 6 (skipn (S i) t)) = 6%nat) by (rewrite E1; reflexivity).
  rewrite length_firstn, length_skipn in E. lia.
- destruct (ci_eqb (firstn 6 (skipn i t)) prefix_lc &&
    match i with O => true | S i' => is_space (byte_at t i') end) eqn:E2; [|discriminate].
  injection H as <-. apply andb_true_iff in E2 as [E2 _].
  apply readings_scan.ci_len in E2. rewrite length_firstn, length_skipn in E2.
  change (length prefix_lc) with 6%nat in E2. lia.
Qed.

(* ---- the branch decisions, each on one byte: a closed valuation over the 256 byte values ----
   atom 33 is the byte P, the first and the third loop load, atom 12 the byte the second loop holds in a2 *)
Definition pp_E00 : env := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []).
Definition pp_Eb (c : Z) : env := ewset pp_E00 33 (Z_to_bv 64 c).
Definition pp_En (c : Z) : env := ewset pp_E00 12 (Z_to_bv 64 c).
Definition pp_Db (cnd : branch_cond) (a b : sv) (c : Z) : bool :=
  branch_taken cnd (sv_denot (pp_Eb c) a) (sv_denot (pp_Eb c) b).
Definition pp_Dn (cnd : branch_cond) (a b : sv) (c : Z) : bool :=
  branch_taken cnd (sv_denot (pp_En c) a) (sv_denot (pp_En c) b).

Lemma pp_Db_of : forall E c cnd a b, ew E 33 = Z_to_bv 64 c ->
  sv_atoms_in (Nat.eqb 33) a = true -> sv_atoms_in (Nat.eqb 33) b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = pp_Db cnd a b c.
Proof.
intros E c cnd a b HE Ha Hb. unfold pp_Db.
assert (HA : env_agree_on (Nat.eqb 33) E (pp_Eb c)).
{ intros n Hn. apply Nat.eqb_eq in Hn. subst n. unfold pp_Eb. rewrite ew_ewset_same. symmetry. exact HE. }
rewrite (sv_denot_agree_on _ _ _ a HA Ha), (sv_denot_agree_on _ _ _ b HA Hb). reflexivity.
Qed.

Lemma pp_Dn_of : forall E c cnd a b, ew E 12 = Z_to_bv 64 c ->
  sv_atoms_in (Nat.eqb 12) a = true -> sv_atoms_in (Nat.eqb 12) b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = pp_Dn cnd a b c.
Proof.
intros E c cnd a b HE Ha Hb. unfold pp_Dn.
assert (HA : env_agree_on (Nat.eqb 12) E (pp_En c)).
{ intros n Hn. apply Nat.eqb_eq in Hn. subst n. unfold pp_En. rewrite ew_ewset_same. symmetry. exact HE. }
rewrite (sv_denot_agree_on _ _ _ a HA Ha), (sv_denot_agree_on _ _ _ b HA Hb). reflexivity.
Qed.

(* P and the first and third loops: `addi a, c, -9; bgeu a, s3` then `bne c, s2` is isspace; `bne c, 60` is '<' *)
Definition pp_d9 (c : Z) : bool := pp_Db BC_GEU (SOff 33 (-9)) (SLit 5) c.
Definition pp_d32 (c : Z) : bool := pp_Db BC_NE (SOff 33 0) (SLit 32) c.
Definition pp_d60 (c : Z) : bool := pp_Db BC_NE (SOff 33 0) (SLit 60) c.
Definition pp_bok (c : Z) : bool :=
  implb (negb (pp_d9 c)) (is_space c) &&
  implb (pp_d9 c && negb (pp_d32 c)) (is_space c) &&
  implb (pp_d9 c && pp_d32 c) (negb (is_space c)).
Definition pp_lok (c : Z) : bool :=
  implb (negb (pp_d60 c)) (c =? 60) && implb (pp_d60 c) (negb (c =? 60)).

(* the second loop: `bltu s7, c & 255` is a name byte; else bit c of s4 = RD_MASK1 is NUL-or-space; else `beq c, s7` *)
Definition pp_c58 : sv := SAlu ALU_AND (SOff 12 0) (SLit 255).
Definition pp_mk : sv := SAlu ALU_AND (SAlu ALU_SRL (SLit RD_MASK1) pp_c58) (SLit 1).
Definition pp_dgt (c : Z) : bool := pp_Dn BC_LTU (SLit 58) pp_c58 c.
Definition pp_dmk (c : Z) : bool := pp_Dn BC_NE pp_mk (SLit 0) c.
Definition pp_deq (c : Z) : bool := pp_Dn BC_EQ pp_c58 (SLit 58) c.
Definition pp_nok (c : Z) : bool :=
  implb (pp_dgt c) (name_ok c) &&
  implb (negb (pp_dgt c) && pp_dmk c) (negb (name_ok c) && negb (c =? 58)) &&
  implb (negb (pp_dgt c) && negb (pp_dmk c) && pp_deq c) (c =? 58) &&
  implb (negb (pp_dgt c) && negb (pp_dmk c) && negb (pp_deq c)) (name_ok c && negb (c =? 58)).

Lemma pp_all256 : forall (g : Z -> bool), forallb g (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> g c = true.
Proof.
intros g H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff.
exists (Z.to_nat c). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Lemma pp_bok_all : forall c, 0 <= c < 256 -> pp_bok c = true.
Proof. apply pp_all256. vm_compute. reflexivity. Qed.
Lemma pp_lok_all : forall c, 0 <= c < 256 -> pp_lok c = true.
Proof. apply pp_all256. vm_compute. reflexivity. Qed.
Lemma pp_nok_all : forall c, 0 <= c < 256 -> pp_nok c = true.
Proof. apply pp_all256. vm_compute. reflexivity. Qed.

Ltac pp_bok_tac c Hc :=
  intros; pose proof (pp_bok_all c Hc) as X; unfold pp_bok in X;
  repeat match goal with H : pp_d9 c = _ |- _ => rewrite H in X; clear H end;
  repeat match goal with H : pp_d32 c = _ |- _ => rewrite H in X; clear H end;
  repeat match goal with H : pp_d60 c = _ |- _ => rewrite H in X; clear H end;
  cbn [negb andb implb] in X; destruct (is_space c); first [reflexivity | discriminate X].
Ltac pp_nok_tac c Hc :=
  intros; pose proof (pp_nok_all c Hc) as X; unfold pp_nok in X;
  repeat match goal with H : pp_dgt c = _ |- _ => rewrite H in X; clear H end;
  repeat match goal with H : pp_dmk c = _ |- _ => rewrite H in X; clear H end;
  repeat match goal with H : pp_deq c = _ |- _ => rewrite H in X; clear H end;
  cbn [negb andb implb] in X.

Lemma pp_sp_in : forall c, 0 <= c < 256 -> pp_d9 c = false -> is_space c = true.
Proof. intros c Hc. pp_bok_tac c Hc. Qed.
Lemma pp_sp_32 : forall c, 0 <= c < 256 -> pp_d9 c = true -> pp_d32 c = false -> is_space c = true.
Proof. intros c Hc. pp_bok_tac c Hc. Qed.
Lemma pp_sp_no : forall c, 0 <= c < 256 -> pp_d9 c = true -> pp_d32 c = true -> is_space c = false.
Proof. intros c Hc. pp_bok_tac c Hc. Qed.
Lemma pp_lt_yes : forall c, 0 <= c < 256 -> pp_d60 c = false -> c = 60.
Proof.
intros c Hc H60. pose proof (pp_lok_all c Hc) as X. unfold pp_lok in X. rewrite H60 in X.
cbn [negb implb] in X. apply andb_true_iff in X as [X _]. apply Z.eqb_eq in X. exact X.
Qed.
Lemma pp_lt_no : forall c, 0 <= c < 256 -> pp_d60 c = true -> c <> 60.
Proof.
intros c Hc H60. pose proof (pp_lok_all c Hc) as X. unfold pp_lok in X. rewrite H60 in X.
cbn [negb implb] in X. apply andb_true_iff in X as [_ X]. apply Bool.negb_true_iff, Z.eqb_neq in X. exact X.
Qed.

Lemma pp_nm_gt : forall c, 0 <= c < 256 -> pp_dgt c = true -> name_ok c = true.
Proof. intros c Hc. pp_nok_tac c Hc. destruct (name_ok c); first [reflexivity | discriminate X]. Qed.
Lemma pp_nm_mk : forall c, 0 <= c < 256 -> pp_dgt c = false -> pp_dmk c = true ->
  name_ok c = false /\ c <> 58.
Proof.
intros c Hc. pp_nok_tac c Hc.
destruct (name_ok c); [discriminate X|]. split; [reflexivity|].
destruct (Z.eqb_spec c 58); [cbn [negb andb] in X; discriminate X | exact n].
Qed.
Lemma pp_nm_eq : forall c, 0 <= c < 256 -> pp_dgt c = false -> pp_dmk c = false -> pp_deq c = true -> c = 58.
Proof.
intros c Hc. pp_nok_tac c Hc. destruct (Z.eqb_spec c 58); [exact e | discriminate X].
Qed.
Lemma pp_nm_ok : forall c, 0 <= c < 256 -> pp_dgt c = false -> pp_dmk c = false -> pp_deq c = false ->
  name_ok c = true /\ c <> 58.
Proof.
intros c Hc. pp_nok_tac c Hc.
destruct (name_ok c); [|discriminate X]. split; [reflexivity|].
destruct (Z.eqb_spec c 58); [cbn [negb andb] in X; discriminate X | exact n].
Qed.

(* ======== the entry lemmas of the cut states ======== *)
Definition pp_extra (u2v c q : Z) : list word := [w64 u2v; w64 c; w64 q].

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* rd_loop's pinned constants *)
Definition pp_pins (regs : bvmap 5 word) : Prop :=
  getr regs 8 = w64 RD_M1 /\ getr regs 18 = w64 32 /\ getr regs 19 = w64 5 /\ getr regs 20 = w64 RD_MASK1 /\
  getr regs 23 = w64 58.

Lemma pp_regs_ok : forall regs extra, pp_pins regs -> regs_ok (Ereg regs extra) pp_regs0 regs.
Proof.
intros regs extra (R8 & R18 & R19 & R20 & R23). unfold pp_regs0.
repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg | ..];
  cbn [sv_denot]; first [exact R8 | exact R18 | exact R19 | exact R20 | exact R23].
Qed.

(* the frame word this walk reads, and where the frame lies *)
Definition pp_fr (W : world tfibsegs) (mem : word -> option byte) (F u2v : Z) : Prop :=
  val_mem tfibsegs (mrestrict (w_H W) mem) (F + 0x58) 8 u2v /\ 0 <= u2v < 2 ^ 64 /\
  alloc_ceiling <= F /\ F + 0x68 <= 2 ^ 47 /\ F mod 16 = 0.

Lemma pp_chunk8 : forall E m b off (e : sv) v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m (b + off) 8 v ->
  YP09.chunk_ok tfibsegs E m b (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E m b off e v He Hv Hm. apply (chunk_ok_val tfibsegs E m b off 8%N e v He); [cbn; lia | cbn; lia | exact Hm].
Qed.

Lemma pp_frameR_ok : forall E m F u2v,
  bv_unsigned (ew E 2) = F -> ew E 32 = w64 u2v -> 0 <= u2v < 2 ^ 64 -> 0 <= F -> F + 0x68 <= 2 ^ 64 ->
  val_mem tfibsegs m (F + 0x58) 8 u2v -> region_ok tfibsegs E m pp_frameR.
Proof.
intros E m F u2v U2 E32 Hu2 HF0 HF1 V58. unfold pp_frameR, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (pp_chunk8 E _ F 0x58 (SOff 32 0) u2v);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | lia | exact V58].
Qed.

Lemma pp_sc48_ok : forall E m F,
  bv_unsigned (ew E 2) = F -> 0 <= F -> F + 0x68 <= 2 ^ 64 ->
  (forall a, F + 0x48 <= a < F + 0x50 -> writable_at tfibsegs m a) -> region_ok tfibsegs E m pp_sc48.
Proof.
intros E m F U2 HF0 HF1 HW. unfold pp_sc48, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia|]. apply Forall_nil.
Qed.

Lemma pp_byteR_ok : forall E m n off p c,
  bv_unsigned (ew E n) = p -> ew E 33 = w64 c -> 0 <= c < 256 -> 0 <= p + off -> p + off + 1 <= 2 ^ 64 ->
  val_mem tfibsegs m (p + off) 1 c -> region_ok tfibsegs E m (pp_byte n off).
Proof.
intros E m n off p c Un E33 Hc Hlo Hhi Vc. unfold pp_byte, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Un.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs E m p off 1%N (SOff 33 0) c);
  [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
  | cbn; lia | cbn; lia | exact Vc].
Qed.

Ltac pp_uw E n v H :=
  assert (bv_unsigned (ew E n) = v) by (rewrite H; apply unsigned_lit_small; try unfold SHADOW_OFF; lia).
Ltac pp_ereg E regs n R :=
  assert (ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))) by
    (unfold E; apply ew_Ereg_nat; rewrite Z_to_bv_unsigned; reflexivity);
  match goal with H : ew E n = getr regs _ |- _ => rewrite R in H end.
Ltac pp_atoms_tac :=
  cbn [f_atoms atoms_ok PP_AF2 PP_AF27 pp_afstr pp_afbyte]; unfold afact_ok; cbn [af_lo af_hi af_al2];
  repeat match goal with H : bv_unsigned (ew _ ?n) = ?v |- _ => rewrite H end;
  change (2 ^ 4) with 16; rewrite ?Z.pow_0_r, ?Z.mod_1_r; unfold SHADOW_OFF; repeat split; lia.
Ltac pp_disj_tac :=
  apply pairwise_disjoint_of_extents;
  unfold pp_frameR, pp_byte, pp_sc48, extent_of_region;
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val];
  repeat match goal with H : bv_unsigned (ew _ ?n) = ?v |- _ => rewrite H end;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.

Lemma pp_entry_P : forall pc (W : world tfibsegs) regs mem F u2v s11 atv c,
  pp_fr W mem F u2v ->
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> pp_pins regs ->
  getr regs 21 = w64 atv -> getr regs 10 = w64 s11 -> 0 <= s11 <= 7 ->
  4096 <= atv -> atv + s11 + 1 <= alloc_ceiling -> 0 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (atv + s11) 1 c ->
  st_ok tfibsegs (Ereg regs (pp_extra u2v c (atv + s11))) (ss_pp_Pat pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros pc W regs mem F u2v s11 atv c (V58 & Hu2 & HFc & HF2 & HF16) R2 R27 HPN R21 R10 Hs11 Hat Hatc Hc Vc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs (pp_extra u2v c (atv + s11))).
assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E21 : ew E 21 = w64 atv) by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E10 : ew E 10 = w64 s11) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E32 : ew E 32 = w64 u2v) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (atv + s11)) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
pp_uw E 2%nat F E2. pp_uw E 27%nat SHADOW_OFF E27. pp_uw E 21%nat atv E21. pp_uw E 10%nat s11 E10.
pp_uw E 33%nat c E33. pp_uw E 34%nat (atv + s11) E34.
unfold ss_pp_Pat. apply (entry_st_ok_full tfibsegs); change (Ereg regs (pp_extra u2v c (atv + s11))) with E.
- apply pp_regs_ok. exact HPN.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (pp_frameR_ok E _ F u2v); try assumption; try lia.
  + apply (pp_byteR_ok E _ 34 0 (atv + s11) c); try assumption; try lia. rewrite Z.add_0_r. exact Vc.
- pp_disj_tac.
- split; [|split; [exact I|]].
  + pp_atoms_tac.
  + cbn [f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj.
      rewrite (U_add_off_atom E 21 0 10 0) by
        (repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end; unfold M64; lia).
      rewrite (U_atom E 34 (atv + s11) E34 ltac:(lia)).
      repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end. lia.
    * apply U_inj.
      rewrite (U_add_off_atom E 10 0 21 0) by
        (repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end; unfold M64; lia).
      rewrite (U_atom E 34 (atv + s11) E34 ltac:(lia)).
      repeat match goal with H : bv_unsigned (ew E ?n) = ?v |- _ => rewrite H end. lia.
Qed.

Lemma pp_entry_L1 : forall (W : world tfibsegs) regs mem F pk c,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> pp_pins regs ->
  alloc_ceiling <= F -> F + 0x68 <= 2 ^ 47 -> F mod 16 = 0 ->
  getr regs 11 = w64 pk -> getr regs 22 = w64 pk ->
  4096 <= pk -> pk + 1 <= alloc_ceiling -> 0 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) pk 1 c ->
  st_ok tfibsegs (Ereg regs (pp_extra 0 c 0)) ss_pp_L1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PP_L1) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem F pk c R2 R27 HPN HFc HF2 HF16 R11 R22 Hpk Hpkc Hc Vc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs (pp_extra 0 c 0)).
assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E11 : ew E 11 = w64 pk) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E22 : ew E 22 = w64 pk) by (unfold E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E33 : ew E 33 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
pp_uw E 2%nat F E2. pp_uw E 27%nat SHADOW_OFF E27. pp_uw E 11%nat pk E11. pp_uw E 22%nat pk E22.
pp_uw E 33%nat c E33.
unfold ss_pp_L1. apply (entry_st_ok_full tfibsegs); change (Ereg regs (pp_extra 0 c 0)) with E.
- apply pp_regs_ok. exact HPN.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (pp_byteR_ok E _ 22 0 pk c); try assumption; try lia. rewrite Z.add_0_r. exact Vc.
- apply pairwise_disjoint_of_extents. unfold pp_byte, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. pp_atoms_tac.
Qed.

Lemma pp_entry_L2 : forall (W : world tfibsegs) regs mem F c qa sv cn,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> pp_pins regs ->
  alloc_ceiling <= F -> F + 0x68 <= 2 ^ 47 -> F mod 16 = 0 ->
  getr regs 12 = w64 c -> getr regs 10 = w64 qa -> getr regs 24 = w64 sv ->
  0 <= c < 256 -> 4096 <= qa -> qa + 1 <= alloc_ceiling -> 4096 <= sv -> sv + 2 <= alloc_ceiling ->
  0 <= cn < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem) (sv + 1) 1 cn ->
  st_ok tfibsegs (Ereg regs (pp_extra 0 cn 0)) ss_pp_L2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PP_L2) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem F c qa sv cn R2 R27 HPN HFc HF2 HF16 R12 R10 R24 Hc Hqa Hqac Hsv Hsvc Hcn Vc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs (pp_extra 0 cn 0)).
assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E12 : ew E 12 = w64 c) by (unfold E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
assert (E10 : ew E 10 = w64 qa) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E24 : ew E 24 = w64 sv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E33 : ew E 33 = w64 cn) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
pp_uw E 2%nat F E2. pp_uw E 27%nat SHADOW_OFF E27. pp_uw E 12%nat c E12. pp_uw E 10%nat qa E10.
pp_uw E 24%nat sv E24. pp_uw E 33%nat cn E33.
unfold ss_pp_L2. apply (entry_st_ok_full tfibsegs); change (Ereg regs (pp_extra 0 cn 0)) with E.
- apply pp_regs_ok. exact HPN.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (pp_byteR_ok E _ 24 1 sv cn); try assumption; try lia.
- apply pairwise_disjoint_of_extents. unfold pp_byte, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. pp_atoms_tac.
Qed.

Lemma pp_entry_L2x : forall (W : world tfibsegs) regs mem F c qa sv,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> pp_pins regs ->
  alloc_ceiling <= F -> F + 0x68 <= 2 ^ 47 -> F mod 16 = 0 ->
  getr regs 12 = w64 c -> getr regs 10 = w64 qa -> getr regs 24 = w64 sv ->
  0 <= c < 256 -> 4096 <= qa -> qa + 1 <= alloc_ceiling -> 4096 <= sv -> sv + 2 <= alloc_ceiling ->
  st_ok tfibsegs (Ereg regs (pp_extra 0 0 0)) ss_pp_L2x
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PP_L2) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem F c qa sv R2 R27 HPN HFc HF2 HF16 R12 R10 R24 Hc Hqa Hqac Hsv Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs (pp_extra 0 0 0)).
assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E12 : ew E 12 = w64 c) by (unfold E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
assert (E10 : ew E 10 = w64 qa) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E24 : ew E 24 = w64 sv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
pp_uw E 2%nat F E2. pp_uw E 27%nat SHADOW_OFF E27. pp_uw E 12%nat c E12. pp_uw E 10%nat qa E10.
pp_uw E 24%nat sv E24.
unfold ss_pp_L2x. apply (entry_st_ok_full tfibsegs); change (Ereg regs (pp_extra 0 0 0)) with E.
- apply pp_regs_ok. exact HPN.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. pp_atoms_tac.
Qed.

Lemma pp_entry_L3E : forall (W : world tfibsegs) regs mem F sv,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> pp_pins regs ->
  alloc_ceiling <= F -> F + 0x68 <= 2 ^ 47 -> F mod 16 = 0 ->
  (forall a, F + 0x48 <= a < F + 0x50 -> writable_at tfibsegs (mrestrict (w_H W) mem) a) ->
  getr regs 24 = w64 sv -> 4096 <= sv -> sv + 1 <= alloc_ceiling ->
  st_ok tfibsegs (Ereg regs []) ss_pp_L3E
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PP_L3E) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem F sv R2 R27 HPN HFc HF2 HF16 HW R24 Hsv Hsvc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E24 : ew E 24 = w64 sv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
pp_uw E 2%nat F E2. pp_uw E 27%nat SHADOW_OFF E27. pp_uw E 24%nat sv E24.
unfold ss_pp_L3E. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
- apply pp_regs_ok. exact HPN.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. apply (pp_sc48_ok E _ F); try assumption; lia.
- apply pairwise_disjoint_of_extents. unfold pp_sc48, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. pp_atoms_tac.
Qed.

Lemma pp_entry_L3 : forall (W : world tfibsegs) regs mem F sv c,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> pp_pins regs ->
  alloc_ceiling <= F -> F + 0x68 <= 2 ^ 47 -> F mod 16 = 0 ->
  getr regs 24 = w64 sv -> 4096 <= sv -> sv + 2 <= alloc_ceiling -> 0 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (sv + 1) 1 c ->
  st_ok tfibsegs (Ereg regs (pp_extra 0 c 0)) ss_pp_L3
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PP_L3) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem F sv c R2 R27 HPN HFc HF2 HF16 R24 Hsv Hsvc Hc Vc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs (pp_extra 0 c 0)).
assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E24 : ew E 24 = w64 sv) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E33 : ew E 33 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
pp_uw E 2%nat F E2. pp_uw E 27%nat SHADOW_OFF E27. pp_uw E 24%nat sv E24. pp_uw E 33%nat c E33.
unfold ss_pp_L3. apply (entry_st_ok_full tfibsegs); change (Ereg regs (pp_extra 0 c 0)) with E.
- apply pp_regs_ok. exact HPN.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (pp_byteR_ok E _ 24 1 sv c); try assumption; try lia.
- apply pairwise_disjoint_of_extents. unfold pp_byte, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. pp_atoms_tac.
Qed.

Lemma pp_entry_ST : forall (W : world tfibsegs) regs mem F qa,
  getr regs 2 = w64 F -> getr regs 27 = w64 SHADOW_OFF -> pp_pins regs ->
  alloc_ceiling <= F -> F + 0x68 <= 2 ^ 47 -> F mod 16 = 0 ->
  getr regs 10 = w64 qa -> 4096 <= qa -> qa + 1 <= alloc_ceiling ->
  st_ok tfibsegs (Ereg regs []) ss_pp_ST
    (restrict (w_H W) (mkst regs (Z_to_bv 64 PP_ST) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem F qa R2 R27 HPN HFc HF2 HF16 R10 Hqa Hqac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (E2 : ew E 2 = w64 F) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E27 : ew E 27 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E10 : ew E 10 = w64 qa) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
pp_uw E 2%nat F E2. pp_uw E 27%nat SHADOW_OFF E27. pp_uw E 10%nat qa E10.
unfold ss_pp_ST. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
- apply pp_regs_ok. exact HPN.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. pp_atoms_tac.
Qed.

(* ---- the text string: a byte at an index up to its NUL, and a suffix as a C string ---- *)
Lemma pp_val_at : forall (W : world tfibsegs) mem p l j, cstr_ok tfibsegs W mem p l -> (j <= length l)%nat ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat j) 1 (byte_at l j) /\ 0 <= byte_at l j < 256.
Proof.
intros W mem p l j ((Hg & _) & _) Hj.
destruct (Hg j ltac:(rewrite length_app; cbn [length]; lia)) as [Hv Hr].
destruct (Nat.lt_ge_cases j (length l)) as [H|H].
- rewrite app_nth1 in Hv, Hr by lia. split; [exact Hv | exact Hr].
- assert (Hje : j = length l) by lia. subst j.
  rewrite nth_middle in Hv, Hr.
  unfold byte_at. rewrite nth_overflow by lia. split; [exact Hv | lia].
Qed.

Lemma pp_div8_mono : forall a b, a <= b -> a / 8 * 8 <= b / 8 * 8.
Proof. intros a b H. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma pp_cstr_suffix : forall (W : world tfibsegs) mem p l k,
  cstr_ok tfibsegs W mem p l -> (k <= length l)%nat ->
  cstr_ok tfibsegs W mem (p + Z.of_nat k) (skipn k l).
Proof.
intros W mem p l k ((Hg & Hnz) & H4 & Hc & H32 & Ham & Hra & Hhv & Htl) Hk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlen : Z.of_nat (length (skipn k l)) = Z.of_nat (length l) - Z.of_nat k)
  by (rewrite length_skipn; lia).
assert (Hsk : skipn k l ++ [0] = skipn k (l ++ [0])).
{ rewrite skipn_app. replace (k - length l)%nat with 0%nat by lia. reflexivity. }
split; [split|].
- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. rewrite length_skipn in Hj.
  rewrite Hsk, pp_nth_skipn.
  replace (p + Z.of_nat k + Z.of_nat j) with (p + Z.of_nat (k + j)%nat) by lia.
  apply Hg. rewrite length_app. cbn [length]. lia.
- apply readings_scan.Forall_skipn_z. exact Hnz.
- split; [lia|]. split; [lia|]. split; [lia|]. split.
  { unfold amem_range in Ham |- *. lia. }
  split; [eapply range_addressable_sub; [exact Hra | lia | lia]|].
  split.
  { intros s Hs. apply Hhv.
    assert (Hup : p + Z.of_nat k + (Z.of_nat (length (skipn k l)) + 1) - 1
                  = p + (Z.of_nat (length l) + 1) - 1) by lia.
    rewrite Hup in Hs.
    pose proof (pp_div8_mono (shadow_addr p) (shadow_addr (p + Z.of_nat k))
      ltac:(unfold shadow_addr; pose proof (Z.div_le_mono p (p + Z.of_nat k) 8 ltac:(lia) ltac:(lia)); lia)).
    lia. }
  intros a Ha. rewrite Hlen in Ha.
  replace (p + Z.of_nat k + (Z.of_nat (length l) - Z.of_nat k)) with (p + Z.of_nat (length l)) in Ha by lia.
  apply Htl. exact Ha.
Qed.

Lemma pp_w64_of_U : forall (E : env) v z, U E v = zcanon z -> sv_denot E v = w64 z.
Proof.
intros E v z H. apply bv_eq. unfold U in H. rewrite H. unfold w64. rewrite Z_to_bv_unsigned.
apply zcanon_wrap.
Qed.

Lemma pp_U_Bx : forall (E : env), ew E 27 = w64 SHADOW_OFF -> U E PP_Bx = SHADOW_OFF.
Proof. intros E H. unfold PP_Bx. apply (U_atom E 27 SHADOW_OFF H). unfold SHADOW_OFF. lia. Qed.

(* every inline check of this walk is one byte of the text string *)
Lemma pp_obl1 : forall (W : world tfibsegs) mem (E : env) (v : sv) t tb,
  cstr_ok tfibsegs W mem t tb -> U E PP_Bx = SHADOW_OFF ->
  t <= U E v -> U E v + 1 <= t + Z.of_nat (length tb) + 1 ->
  ob_holds tfibsegs PP_Bx E (mrestrict (w_H W) mem) (mkOB v 1).
Proof.
intros W mem E v t tb (_ & _ & _ & _ & _ & Hra & _) HB Hlo Hhi.
unfold ob_holds. cbn [ob_x ob_n].
exact (obl_of_range tfibsegs (w_H W) mem E PP_Bx (U E v) 1 t (Z.of_nat (length tb) + 1) Hra HB Hlo ltac:(lia)).
Qed.

End e.

(* ---- the values the engine computes are linear in the entry atoms: U of each form ---- *)
Section u. Context {fx : YK11.FPState}.
Lemma pp_U_off : forall (E : env) n z c, ew E n = w64 z -> U E (SOff n c) = zcanon (z + c).
Proof.
intros E n z c H. rewrite U_SOff, H. unfold w64. rewrite Z_to_bv_unsigned.
rewrite <- (zcanon_wrap z). unfold zcanon, M64. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma pp_U_add : forall (E : env) a b x y,
  U E a = zcanon x -> U E b = zcanon y -> U E (SAlu ALU_ADD a b) = zcanon (x + y).
Proof.
intros E a b x y Ha Hb. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb.
unfold zcanon, M64. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma pp_U_sub : forall (E : env) a b x y,
  U E a = zcanon x -> U E b = zcanon y -> U E (SAlu ALU_SUB a b) = zcanon (x - y).
Proof.
intros E a b x y Ha Hb. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb.
unfold zcanon, M64. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.
Lemma pp_U_mul : forall (E : env) a b x y,
  U E a = zcanon x -> U E b = zcanon y -> U E (SMd M_MUL a b) = zcanon (x * y).
Proof.
intros E a b x y Ha Hb. rewrite U_SMd. cbn [zmd_raw]. rewrite Ha, Hb.
unfold zcanon, M64. rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r. reflexivity.
Qed.
Lemma pp_U_lit : forall (E : env) z, U E (SLit z) = zcanon z.
Proof. intros E z. apply U_SLit. Qed.
Lemma pp_zcanon_eq : forall x y, x mod M64 = y mod M64 -> zcanon x = zcanon y.
Proof. intros x y H. unfold zcanon. exact H. Qed.
Lemma pp_zc_neg : forall k, 2 ^ 63 <= k < 2 ^ 64 -> zcanon k = zcanon (k - 18446744073709551616).
Proof.
intros k Hk. apply pp_zcanon_eq. unfold M64.
rewrite <- (Z_mod_plus_full (k - 18446744073709551616) 1 (2 ^ 64)). f_equal. lia.
Qed.
(* a literal or an offset at or above 2^63 is a negative number *)
Lemma pp_U_lit_neg : forall (E : env) z, 2 ^ 63 <= z < 2 ^ 64 -> U E (SLit z) = zcanon (z - 18446744073709551616).
Proof. intros E z Hz. rewrite pp_U_lit. apply pp_zc_neg. exact Hz. Qed.
Lemma pp_U_off_neg : forall (E : env) n z c, ew E n = w64 z -> 2 ^ 63 <= c < 2 ^ 64 ->
  U E (SOff n c) = zcanon (z + (c - 18446744073709551616)).
Proof.
intros E n z c H Hc. rewrite (pp_U_off E n z c H). apply pp_zcanon_eq. unfold M64.
rewrite <- (Z_mod_plus_full (z + (c - 18446744073709551616)) 1 (2 ^ 64)). f_equal. lia.
Qed.
Lemma pp_mod_k : forall x y k, x = y + k * M64 -> x mod M64 = y mod M64.
Proof. intros x y k ->. apply Z_mod_plus_full. Qed.

(* the UBSan guards (B5's lib/B/FMTrapB.v classes K1 fmt_eq_not, K1n fmt_ne_taken): a text position is not -1 *)
Lemma pp_g_eq : forall (E : env) n z c, ew E n = w64 z -> 0 <= z + c < RD_M1 ->
  branch_taken BC_EQ (sv_denot E (SOff n c)) (sv_denot E (SLit 18446744073709551615)) = false.
Proof.
intros E n z c H Hz. apply fmt_eq_not. rewrite (pp_U_off E n z c H), U_SLit.
unfold zcanon, M64, RD_M1 in *. rewrite (Z.mod_small (z + c)) by lia.
change (18446744073709551615 mod 2 ^ 64) with 18446744073709551615. lia.
Qed.
Lemma pp_g_ne : forall (E : env) n z c, ew E n = w64 z -> 0 <= z + c < RD_M1 ->
  branch_taken BC_NE (sv_denot E (SOff n c)) (sv_denot E (SLit 18446744073709551615)) = true.
Proof.
intros E n z c H Hz. apply fmt_ne_taken. rewrite (pp_U_off E n z c H), U_SLit.
unfold zcanon, M64, RD_M1 in *. rewrite (Z.mod_small (z + c)) by lia.
change (18446744073709551615 mod 2 ^ 64) with 18446744073709551615. lia.
Qed.
End u.

(* the bytes consumed after p0 at the second loop's head (m name bytes after p1) and at the third's (j spaces after
   the ':' at p2) *)
Definition pp_s10_L2 (i s11 p1 m : nat) : Z := Z.of_nat p1 - Z.of_nat i - Z.of_nat s11 + Z.of_nat m.
Definition pp_s10_L3 (i s11 p2 j : nat) : Z := Z.of_nat p2 - Z.of_nat i - Z.of_nat s11 + Z.of_nat j.

Ltac pp_uw E n v H :=
  assert (bv_unsigned (ew E n) = v) by (rewrite H; apply unsigned_lit_small; try unfold SHADOW_OFF; lia).

(* read one register of the state and name the symbolic value the engine computed *)
Ltac pp_rd HS r name :=
  lazymatch type of HS with
  | st_ok ?segs ?Ev ?ss (restrict ?H ?ms) =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      assert (name : getr (ms_regs ms) r = sv_denot Ev e)
        by (rewrite (st_ok_restrict_reg segs H Ev ss ms r HS); reflexivity)
  end.
(* lift an `ew E n = _` fact of the entry env to the env the run extended *)
Ltac pp_lift HS name n H :=
  lazymatch type of HS with
  | st_ok _ ?Ev _ _ => assert (name : ew Ev n = _) by (cbn [ew ewset extK Nat.eqb]; exact H)
  end.

(* U of an engine value, from the facts `ew _ n = w64 z` about the entry env *)
Ltac pp_U_ev :=
  lazymatch goal with
  | |- U ?E (SOff ?n ?c) = _ =>
      match goal with H : ew _ n = w64 ?z |- _ =>
        let Hl := fresh "Hl" in
        assert (Hl : ew E n = w64 z) by (cbn [ew ewset extK Nat.eqb]; exact H);
        first [ exact (pp_U_off_neg E n z c Hl ltac:(lia)) | exact (pp_U_off E n z c Hl) ]
      end
  | |- U ?E (SLit ?z) = _ => first [ exact (pp_U_lit_neg E z ltac:(lia)) | exact (pp_U_lit E z) ]
  | |- U ?E (SAlu ALU_ADD ?a ?b) = _ => eapply pp_U_add; [pp_U_ev | pp_U_ev]
  | |- U ?E (SAlu ALU_SUB ?a ?b) = _ => eapply pp_U_sub; [pp_U_ev | pp_U_ev]
  | |- U ?E (SMd M_MUL ?a ?b) = _ => eapply pp_U_mul; [pp_U_ev | pp_U_ev]
  end.
(* `sv_denot E e = w64 z` for an engine value e *)
Ltac pp_sv :=
  apply pp_w64_of_U; eapply eq_trans; [pp_U_ev | apply pp_zcanon_eq];
  try unfold rd_p0; try unfold pp_s10_L2; try unfold pp_s10_L3; try unfold rd_s10;
  first [ f_equal; lia
        | apply (pp_mod_k _ _ 1); unfold M64; lia
        | apply (pp_mod_k _ _ (-1)); unfold M64; lia ].
(* a register goal after a run: the engine's value for it, then pp_sv *)
Ltac pp_g HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    lazymatch type of HS with st_ok ?segs ?Ev ?ss (restrict ?H ?ms') =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      rewrite (st_ok_restrict_reg segs H Ev ss ms' r HS); change (sr_get (ss_regs ss) r) with e
    end end;
  pp_sv.
(* the run's memory is the entry memory: take the region list from HF's type *)
Ltac pp_fr Hm :=
  lazymatch goal with HF : frame_of _ ?rs _ (ms_mem _) |- _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Hm end;
  cbn [ms_mem] in Hm;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* a branch on the byte atom 33 / 12 as a closed byte decision *)
Ltac pp_decb HS E33 c Hc :=
  let H33 := fresh "H33" in
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (H33 : ew Ev 33 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E33) end;
  erewrite (pp_Db_of _ c _ _ _ H33) in Hc by reflexivity; clear H33.
Ltac pp_decn HS E12 c Hc :=
  let H12 := fresh "H12" in
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (H12 : ew Ev 12 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E12) end;
  erewrite (pp_Dn_of _ c _ _ _ H12) in Hc by reflexivity; clear H12.
(* a UBSan guard arm: the tested register is an entry atom plus an offset, a text position, not -1 *)
Ltac pp_guard Hc :=
  exfalso;
  lazymatch type of Hc with
  | branch_taken BC_EQ (sv_denot ?Ev (SOff ?n ?c)) (sv_denot _ (SLit _)) = true =>
      match goal with H : ew _ n = w64 ?z |- _ =>
        let Hl := fresh "Hl" in
        assert (Hl : ew Ev n = w64 z) by (cbn [ew ewset extK Nat.eqb]; exact H);
        rewrite (pp_g_eq Ev n z c Hl) in Hc by (try unfold rd_p0; unfold RD_M1; lia); discriminate Hc
      end
  | branch_taken BC_NE (sv_denot ?Ev (SOff ?n ?c)) (sv_denot _ (SLit _)) = false =>
      match goal with H : ew _ n = w64 ?z |- _ =>
        let Hl := fresh "Hl" in
        assert (Hl : ew Ev n = w64 z) by (cbn [ew ewset extK Nat.eqb]; exact H);
        rewrite (pp_g_ne Ev n z c Hl) in Hc by (try unfold rd_p0; unfold RD_M1; lia); discriminate Hc
      end
  end.

(* ======== the invariants at the inner cuts, and the statement each one proves ========
   p0 = text + i + s11 is the declaration's first byte (a space); D, the bytes consumed after p0, is
   (the loop-1 spaces) + (the name bytes) + (the loop-3 spaces); s9 = u - 2 - s11 - at - D, s10 = u - 2 - p0 - D. *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).

(* what every state of this segment keeps: the scan's invariant, its accounting, the declaration's head, s5 = at *)
Definition pp_head (cx : rdcx) (i d f s11 : nat) ly3 S3 W3 regs mem md : Prop :=
  rd_loop B cx d ly3 S3 W3 regs mem md /\ rd_acc cx i d f /\
  (i < length (cx_tb cx))%nat /\ head (cx_tb cx) i = Some (i + s11)%nat /\ (s11 = 6 \/ s11 = 7)%nat /\
  is_space (byte_at (cx_tb cx) (i + s11)) = true /\ getr regs 21 = w64 (cx_t cx + Z.of_nat i).

(* the two countdowns after D bytes consumed *)
Definition pp_cd (cx : rdcx) (i s11 : nat) (D : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 25 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - D) /\
  getr regs 26 = w64 (cx_u cx - 2 - rd_p0 cx i s11 - D).

(* L1, 0x82098 (lv2_locate.c:116): k spaces consumed, a1 = s6 = p0 + k, a0 = p0 + k + 1 *)
Definition pp_at_L1 (cx : rdcx) (i d f s11 k : nat) ly3 S3 W3 regs mem md : Prop :=
  let p0 := rd_p0 cx i s11 in let kz := Z.of_nat k in
  pp_head cx i d f s11 ly3 S3 W3 regs mem md /\
  (k <= count_while is_space (skipn (i + s11) (cx_tb cx)))%nat /\
  getr regs 10 = w64 (p0 + kz + 1) /\ getr regs 11 = w64 (p0 + kz) /\ getr regs 22 = w64 (p0 + kz) /\
  pp_cd cx i s11 kz regs.

(* L2, 0x820ec (lv2_locate.c:120): the name's first byte is at p1, m name bytes consumed, a2 holds the byte at
   s8 = p1 + m, a0 = p1 + m + 1, a1 = -m, s6 = text + p1 *)
Definition pp_at_L2 (cx : rdcx) (i d f s11 p1 m : nat) ly3 S3 W3 regs mem md : Prop :=
  pp_head cx i d f s11 ly3 S3 W3 regs mem md /\
  p1 = (i + s11 + count_while is_space (skipn (i + s11) (cx_tb cx)))%nat /\
  (m <= count_while name_ok (skipn p1 (cx_tb cx)))%nat /\
  getr regs 10 = w64 (cx_t cx + Z.of_nat p1 + Z.of_nat m + 1) /\ getr regs 11 = w64 (- Z.of_nat m) /\
  getr regs 12 = w64 (byte_at (cx_tb cx) (p1 + m)) /\ getr regs 22 = w64 (cx_t cx + Z.of_nat p1) /\
  getr regs 24 = w64 (cx_t cx + Z.of_nat p1 + Z.of_nat m) /\ pp_cd cx i s11 (pp_s10_L2 i s11 p1 m) regs.

(* L3E, 0x82150 (lv2_locate.c:121-125): the name ended with ':' at p2 = s8, a1 = p1 - p2 *)
Definition pp_at_L3E (cx : rdcx) (i d f s11 p1 p2 : nat) ly3 S3 W3 regs mem md : Prop :=
  pp_head cx i d f s11 ly3 S3 W3 regs mem md /\
  p1 = (i + s11 + count_while is_space (skipn (i + s11) (cx_tb cx)))%nat /\
  p2 = (p1 + count_while name_ok (skipn p1 (cx_tb cx)))%nat /\ byte_at (cx_tb cx) p2 = 58 /\
  getr regs 11 = w64 (Z.of_nat p1 - Z.of_nat p2) /\ getr regs 22 = w64 (cx_t cx + Z.of_nat p1) /\
  getr regs 24 = w64 (cx_t cx + Z.of_nat p2) /\
  pp_cd cx i s11 (Z.of_nat p2 - Z.of_nat i - Z.of_nat s11) regs.

(* L3, 0x8215c (lv2_locate.c:126): j spaces consumed after the ':' at p2, s8 = p2 + j, F+0x48 = p2 - p1 *)
Definition pp_at_L3 (cx : rdcx) (i d f s11 p1 p2 j : nat) ly3 S3 W3 regs mem md : Prop :=
  pp_head cx i d f s11 ly3 S3 W3 regs mem md /\
  p1 = (i + s11 + count_while is_space (skipn (i + s11) (cx_tb cx)))%nat /\
  p2 = (p1 + count_while name_ok (skipn p1 (cx_tb cx)))%nat /\ byte_at (cx_tb cx) p2 = 58 /\
  (j <= count_while is_space (skipn (S p2) (cx_tb cx)))%nat /\
  rd_slots_ok cx W3 mem [(0x48, Z.of_nat p2 - Z.of_nat p1)] /\
  getr regs 22 = w64 (cx_t cx + Z.of_nat p1) /\ getr regs 24 = w64 (cx_t cx + Z.of_nat p2 + Z.of_nat j) /\
  pp_cd cx i s11 (pp_s10_L3 i s11 p2 j) regs.

(* ST, 0x821ac (lv2_locate.c:127-129): the '<' at p3 found, a0 = text + p3, s8 = text + p3 - 1 *)
Definition pp_at_ST (cx : rdcx) (i d f s11 p1 p2 p3 : nat) ly3 S3 W3 regs mem md : Prop :=
  pp_head cx i d f s11 ly3 S3 W3 regs mem md /\ rd_decl cx i s11 p1 p2 p3 /\
  rd_slots_ok cx W3 mem [(0x48, Z.of_nat p2 - Z.of_nat p1)] /\
  getr regs 10 = w64 (cx_t cx + Z.of_nat p3) /\ getr regs 22 = w64 (cx_t cx + Z.of_nat p1) /\
  getr regs 24 = w64 (cx_t cx + Z.of_nat p3 - 1) /\ pp_cd cx i s11 (rd_s10 i s11 p3) regs.

Definition pp_seg_W1 (f : nat) : Prop :=
  forall cx i d s11 k ly3 S3 W3 regs mem md,
  rd_base B CTX cx -> pp_at_L1 cx i d (S f) s11 k ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L1 regs mem md) (rd_post B cx).
Definition pp_seg_W2 (f : nat) : Prop :=
  forall cx i d s11 p1 m ly3 S3 W3 regs mem md,
  rd_base B CTX cx -> pp_at_L2 cx i d (S f) s11 p1 m ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L2 regs mem md) (rd_post B cx).
Definition pp_seg_L3E (f : nat) : Prop :=
  forall cx i d s11 p1 p2 ly3 S3 W3 regs mem md,
  rd_base B CTX cx -> pp_at_L3E cx i d (S f) s11 p1 p2 ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L3E regs mem md) (rd_post B cx).
Definition pp_seg_W3 (f : nat) : Prop :=
  forall cx i d s11 p1 p2 j ly3 S3 W3 regs mem md,
  rd_base B CTX cx -> pp_at_L3 cx i d (S f) s11 p1 p2 j ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L3 regs mem md) (rd_post B cx).
Definition pp_seg_ST (f : nat) : Prop :=
  forall cx i d s11 p1 p2 p3 ly3 S3 W3 regs mem md,
  rd_base B CTX cx -> pp_at_ST cx i d (S f) s11 p1 p2 p3 ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_ST regs mem md) (rd_post B cx).

(* ---- what every walk of this segment takes out of rd_base and rd_loop ---- *)
Lemma pp_facts_of : forall cx d ly3 S3 W3 regs mem md,
  rd_base B CTX cx -> rd_loop B cx d ly3 S3 W3 regs mem md ->
  pp_fr W3 mem (cx_F cx) (cx_u cx - 2) /\
  getr regs 2 = w64 (cx_F cx) /\ getr regs 27 = w64 SHADOW_OFF /\ pp_pins regs /\
  getr regs 9 = w64 (Z.of_nat d) /\
  cstr_ok tfibsegs W3 mem (cx_t cx) (cx_tb cx) /\ cstr_ok tfibsegs W3 mem (cx_u cx) (cx_ub cx) /\
  4096 <= cx_t cx /\ cx_t cx + Z.of_nat (length (cx_tb cx)) + 8 <= alloc_ceiling /\
  4096 <= cx_u cx /\ cx_u cx + Z.of_nat (length (cx_ub cx)) + 8 <= alloc_ceiling /\
  (forall a, cx_sp cx - STK_readings <= a < cx_sp cx -> writable_at tfibsegs (mrestrict (w_H W3) mem) a) /\
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem md EV_names.
Proof.
intros cx d ly3 S3 W3 regs mem md HB HI.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HAN & _). pose proof HAN as (HAR & _ & _ & _ & _ & Hstk & Hpres & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HI as (HC & R8 & R9 & R18 & R19 & R20 & R23 & HSL & _).
pose proof HC as (HJ & Hk & R2 & _ & _ & R27 & _ & _ & _ & Ct & Cu & _).
change (unpoison [] mem) with mem in HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
unfold rd_slots_ok, rd_loc_list in HSL.
do 5 (apply Forall_cons_iff in HSL; destruct HSL as [_ HSL]).
apply Forall_cons_iff in HSL; destruct HSL as [Hs58 _]. cbn [fst snd] in Hs58.
pose proof Ct as ((_ & _) & Ht4 & Htc & _). pose proof Cu as ((_ & _) & Hu4 & Huc & _).
assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
assert (Hsp : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (FFR : STK_readings = 16624) by reflexivity.
split.
{ unfold pp_fr. split; [apply (proj1 Hs58)|]. split; [lia|]. split; [lia|]. split; [lia|].
  rewrite HF, Hsp. replace (spZ (cx_regs cx) - 208) with (spZ (cx_regs cx) + (-13) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal16. }
split; [exact R2|]. split; [exact R27|].
split; [split; [exact R8|]; split; [exact R18|]; split; [exact R19|]; split; [exact R20 | exact R23]|].
split; [exact R9|].
split; [exact Ct|]. split; [exact Cu|].
split; [exact Ht4|]. split; [lia|]. split; [exact Hu4|]. split; [lia|].
split.
{ intros a Ha. apply (apresent_writable tfibsegs). apply HpresJ. lia. }
exact HJ.
Qed.

(* the scan's invariant across a step of this segment that writes no memory: a fresh journal, the registers the
   invariant carries as themselves (sp, gp, tp, the shadow base) and rd_loop's constants and read_again *)
Definition PP_KEPT : list (bv 5) := [2; 3; 4; 27]%bv.
Lemma pp_loop_keep : forall cx d ly3 S3 W3 regs mem md regs' md',
  rd_loop B cx d ly3 S3 W3 regs mem md ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] ly3 S3 W3 mem md' EV_names ->
  (forall r, In r PP_KEPT -> getr regs' r = getr regs r) ->
  getr regs' 8 = w64 RD_M1 -> getr regs' 9 = w64 (Z.of_nat d) -> getr regs' 18 = w64 32 -> getr regs' 19 = w64 5 ->
  getr regs' 20 = w64 RD_MASK1 -> getr regs' 23 = w64 58 ->
  rd_loop B cx d ly3 S3 W3 regs' mem md'.
Proof.
intros cx d ly3 S3 W3 regs mem md regs' md' HI HJ HR K8 K9 K18 K19 K20 K23.
assert (K2 : getr regs' 2 = getr regs 2) by (apply HR; cbv [PP_KEPT In]; left; apply bv_eq; reflexivity).
assert (K3 : getr regs' 3 = getr regs 3) by (apply HR; cbv [PP_KEPT In]; right; left; apply bv_eq; reflexivity).
assert (K4 : getr regs' 4 = getr regs 4) by (apply HR; cbv [PP_KEPT In]; right; right; left; apply bv_eq; reflexivity).
assert (K27 : getr regs' 27 = getr regs 27)
  by (apply HR; cbv [PP_KEPT In]; right; right; right; left; apply bv_eq; reflexivity).
destruct HI as (HC & R8 & R9 & R18 & R19 & R20 & R23 & HSL & HV & HP & HG & Hcf & Hub & Hwh & Hd).
destruct HC as (HJ0 & Hk & R2 & R3 & R4 & R27 & HSV & K16 & HRO & Ct & Cu & Kt & Ku).
split; [|split; [exact K8 | split; [exact K9 | split; [exact K18 | split; [exact K19 | split; [exact K20 |
  split; [exact K23 | split; [exact HSL | split; [exact HV | split; [exact HP | split; [exact HG |
  split; [exact Hcf | split; [exact Hub | split; [exact Hwh | exact Hd]]]]]]]]]]]]]].
split; [change (unpoison [] mem) with mem; exact HJ|].
split; [exact Hk|]. split; [rewrite K2; exact R2|]. split; [rewrite K3; exact R3|].
split; [rewrite K4; exact R4|]. split; [rewrite K27; exact R27|].
split; [exact HSV|]. split; [exact K16|]. split; [exact HRO|].
split; [exact Ct|]. split; [exact Cu|]. split; [exact Kt | exact Ku].
Qed.

(* a DNone declaration at i: the scan goes on at i + 1 (readings_scan.v sc_none) *)
Lemma pp_to_L : forall f cx i d ly3 S3 W3 regs mem md,
  rd_seg_L B CTX f -> rd_base B CTX cx ->
  rd_loop B cx d ly3 S3 W3 regs mem md -> rd_acc cx i d (S f) ->
  (i < length (cx_tb cx))%nat -> decl (cx_tb cx) i = DNone ->
  getr regs 21 = w64 (cx_t cx + Z.of_nat i + 1) ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_L regs mem md) (rd_post B cx).
Proof.
intros f cx i d ly3 S3 W3 regs mem md HL HB HI (Ha1 & Ha2 & Ha3 & Ha4) Hi Hd R21.
destruct (readings_scan.sc_none (cx_tb cx) (cx_ub cx) i d f Hi Hd) as [Hs Hr].
apply (HL cx (S i) d ly3 S3 W3 regs mem md HB).
split; [exact HI|]. split.
- split; [lia|]. split; [lia|]. split; [rewrite Ha3; exact Hs | rewrite Ha4, Hr; reflexivity].
- rewrite R21. unfold w64. f_equal. lia.
Qed.

End c.
