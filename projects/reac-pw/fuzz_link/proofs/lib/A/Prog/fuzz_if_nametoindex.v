(* fuzz_if_nametoindex (fuzz_link.asan 0x826cc, listing offset AF_fuzz_if_nametoindex = 0x500; listing
   (internal path) (internal record, sha256 c3f31e966607)) and index_of (0x86784,
   AF_index_of = 0x45b8) on image A: the walk of lib/A/Prog/fuzz_if_nametoindex_c.v
   `fuzz_if_nametoindex_acontract` (link_amem.v `aleaf_rd`, K = 8272, EV 0, SIDE []).

   ONE WALK, TWO ENTRIES. The two functions have the same instruction word at every offset but the pc-relative
   ones, and link's listing holds those as PHi / PAddHi / PLdHi / PCall slots over the SAME objects and entries
   (A_OBJ 2 = g_nl, A_OBJ 1 = the .got word of the shadow base, LS___interceptor_trampoline_strcmp,
   LS___asan_report_load4 / 8). So every lemma below takes the entry offset AF with
   `AF = AF_fuzz_if_nametoindex \/ AF = AF_index_of`, destructs it, and runs the same script on both; the index_of walk
   converts the core lemma `if_lookup_aproof` into index_of's contract by unfolding (index_of_c.v states
   index_of_apre / _ard / _awr / _apost word for word the same and INDEX_OF_AK = 8272).

   The code, and what the walk does with it:
   - +0x00..+0x24 the 80-byte frame and the nine saves (ra, s0..s7); +0x28..+0x38 g_nl's address and
     n_if = `lw (g_nl + NK_N_IF)`; +0x3c `blez s3`. The entry state ix_e_ss pins n_if's atom to [0,0] or
     [1, 2^31-1] by the case on `length tab`, so the signed test is decided by the state's own facts and the run
     needs no branch there.
   - the loop at +0x70, one turn per index i: the instrumented check of the 8 bytes of if_name[i] (+0x70..+0x74,
     a token load the shadow entry ix_SH covers), `ld a0, 0(s6)`, `jal wrapper_strcmp` (+0x80, through
     LinkWalkStrcmp.v `aj_gx_astrcmp_at` over lib/Reusable/AStrcmpDef.v `astrcmp_realizes`, the stop index of the
     two C strings from `astrcmp_cstr_meet`), `beqz a0` (+0x84): on a hit the 4-byte check of if_index[i]
     (+0xac..+0xb8) and `lw a0, 0(s4)`; on a miss the six `addi` of +0x88..+0x9c and `bnez s3` (+0xa0).
   - the loop head's state ix_ss carries the ENTRY registers as atoms 0..31 (so the frame's nine chunks are the
     entry values and the epilogue restores `SOff r 0`, which is what `aregs_preserved_of_st_ok` reads), and the
     turn's own values as the extra atoms 32..53. The walk re-enters it at i + 1 from the CONCRETE register
     values the run leaves (`ix_inv`), so the loop is an induction on `length tab - i` and not an unrolling.
   - every exit (n_if = 0, a hit, the last miss) ends at LinkWalk.v `apost_leaf` with E empty: the function
     writes only its own frame, and the strcmp wrapper only [sp' - 2 ESTACK, sp') with sp' = sp - 80, both inside
     [sp - K, sp).

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals) are the image instance's facts, as in pcap's walks;
   STRCMP, wrapper_strcmp's contract at 0x4304c, is discharged by lib/A/Rt/RtStrcmpClosed.v
   `link_astrcmp_closed`.

   Proves fuzz_if_nametoindex (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlk LinkWalkStrcmp fuzz_if_nametoindex_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The link_spec side: the answer of the table walk from index i
   ========================================================================== *)

Lemma ix_list_ext : forall A (l1 l2 : list A), length l1 = length l2 ->
  (forall k, (k < length l1)%nat -> nth_error l1 k = nth_error l2 k) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros [|b l2] Hlen H; cbn [length] in Hlen; try lia;
    [reflexivity|].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [nth_error] in H0. injection H0 as <-.
  f_equal. apply IH; [lia|]. intros k Hk. exact (H (S k) ltac:(cbn; lia)).
Qed.

Lemma ix_skipn_cons : forall A (l : list A) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros A l. induction l as [|a l IH]; intros [|i] x H; cbn [nth_error skipn] in *; try discriminate.
  - injection H as <-. reflexivity.
  - apply IH. exact H.
Qed.

Lemma ix_of_hit : forall tab i n2 iv nm, nth_error tab i = Some (n2, iv) -> n2 = nm ->
  index_of (skipn i tab) nm = iv.
Proof.
  intros tab i n2 iv nm H <-. rewrite (ix_skipn_cons _ tab i _ H). cbn [index_of].
  rewrite bl_eqb_refl. reflexivity.
Qed.

Lemma ix_of_miss : forall tab i n2 iv nm, nth_error tab i = Some (n2, iv) -> n2 <> nm ->
  index_of (skipn i tab) nm = index_of (skipn (S i) tab) nm.
Proof.
  intros tab i n2 iv nm H Hne. rewrite (ix_skipn_cons _ tab i _ H). cbn [index_of].
  destruct (bl_eqb n2 nm) eqn:E; [exfalso; apply Hne; exact (bl_eqb_eq _ _ E) | reflexivity].
Qed.

Lemma ix_of_end : forall tab i nm, (length tab <= i)%nat -> index_of (skipn i tab) nm = 0.
Proof. intros tab i nm H. rewrite skipn_all2 by exact H. reflexivity. Qed.

Lemma ix_nth_some : forall A (l : list A) i, (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof.
  intros A l i Hi. destruct (nth_error l i) as [x|] eqn:E; [exists x; reflexivity|].
  exfalso. apply nth_error_None in E. lia.
Qed.

Lemma ix_set_fs_id : forall (S : astate), S = set_fs (st_fs S) S.
Proof. intros S. destruct S. reflexivity. Qed.

Lemma ix_strcmp_res_cases : forall c1 c2,
  AStrcmpDef.strcmp_res c1 c2 = 0 \/ AStrcmpDef.strcmp_res c1 c2 = -1 \/ AStrcmpDef.strcmp_res c1 c2 = 1.
Proof.
  intros c1 c2. unfold AStrcmpDef.strcmp_res.
  destruct (c1 =? c2); [left; reflexivity|]. destruct (c1 <? c2); [right; left; reflexivity | right; right; reflexivity].
Qed.

(* ==========================================================================
   2. Denotations the walk reads off the symbolic registers
   ========================================================================== *)

Lemma ix_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
  intros E n. apply bv_eq. change (U E (SOff n 0) = bv_unsigned (ew E n)).
  rewrite U_SOff, Z.add_0_r. apply YP0m.zcanon_small.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia.
Qed.

Lemma ix_soffc : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
  intros E n c v Hn Hv Hc. apply bv_eq. change (U E (SOff n c) = bv_unsigned (Z_to_bv 64 (v + c))).
  rewrite U_SOff, Hn, unsigned_lit_small by lia. rewrite unsigned_lit_small by lia.
  apply YP0m.zcanon_small. lia.
Qed.

Definition ix_shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 32 0).

Lemma ix_denot_shx : forall E n v sb, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (sb + v / 8).
Proof.
  intros E n v sb Hn Hm Hv Hsb.
  rewrite (denot_shx E n 32 0 v sb Hn Hm ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite Z.add_0_r. reflexivity.
Qed.

(* the shadow address the entry run builds: `add s7, s5, s7`, the shadow base first *)
Lemma ix_denot_shx_e : forall E n m c v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb ->
  0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
  intros E n m c v sb Hn Hm Hv Hc0 Hc Hsb.
  assert (Hd : 0 <= (v + c) / 8 < 2 ^ 60)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply bv_eq.
  change (U E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3)))
          = bv_unsigned (Z_to_bv 64 (sb + (v + c) / 8))).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
  change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (YP0m.zcanon_small (v + c)) by lia. rewrite (YP0m.zcanon_small ((v + c) / 8)) by lia.
  rewrite (YP0m.zcanon_small sb) by lia. apply YP0m.zcanon_small. lia.
Qed.

(* the same shape after one turn (`addi s7, s7, 1` at +0x94) *)
Lemma ix_denot_shx1 : forall E n v sb, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 32 0)) (SLit 1))
    = Z_to_bv 64 (sb + v / 8 + 1).
Proof.
  intros E n v sb Hn Hm Hv Hsb.
  assert (Hd : 0 <= v / 8 < 2 ^ 60)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply bv_eq.
  change (U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 32 0)) (SLit 1))
          = bv_unsigned (Z_to_bv 64 (sb + v / 8 + 1))).
  rewrite U_SAlu. cbn [zalu_raw].
  change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 32 0)))
    with (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 32 0)))).
  rewrite (ix_denot_shx E n v sb Hn Hm ltac:(lia) ltac:(lia)).
  rewrite (U_lit E 1) by lia. rewrite !unsigned_lit_small by lia.
  apply YP0m.zcanon_small. lia.
Qed.

(* ==========================================================================
   3. The two symbolic states
   ========================================================================== *)

Definition IX_FRAME : Z := 80.
Definition IX_NM_LO : Z := LA_G_NL + NK_IF_NAME.
Definition IX_IX_LO : Z := LA_G_NL + NK_IF_INDEX.

Definition ix_nif_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 2)) NK_N_IF (NK_N_IF + 4) 0 0 [YP09.mkChunk NK_N_IF (CVal 4 (SOff 33 0))].
Definition ix_e_regions : smem := [stack_region IX_FRAME; got_regionP; bcell_regionP 32; ix_nif_region].
Definition ix_e_facts (clo chi : Z) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (A_OBJ 2, mkAF LA_G_NL LA_G_NL 0);
           (32%nat, mkAF SB SB 0); (33%nat, mkAF clo chi 0)] [] [].
Definition ix_e_ss (AF clo chi : Z) : sstate := mkSS AF sr_atoms ix_e_regions None (ix_e_facts clo chi).
Definition ix_e_extra (nif : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 nif].

Definition ix_SH : list shent := [mkSHE 34 0 8; mkSHE 35 0 4].
Definition ix_sr : list sv :=
  [SLit 0;
   SOff 38 0; SOff 2 (-80); SOff 3 0; SOff 4 0;
   SOff 39 0; SOff 40 0; SOff 41 0;
   SOff 10 0; SOff 35 0;
   SOff 42 0; SOff 43 0; SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0;
   SOff 34 0; SOff 33 0; SOff 35 0; SOff 32 0; SOff 34 0; ix_shx (SOff 34 0);
   SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 50 0; SOff 51 0; SOff 52 0; SOff 53 0].
Definition ix_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-80) 0 0 0
    [YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition ix_nmr : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))].
Definition ix_ixr : YP09.region := YP09.mkRegion (Some 35%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))].
Definition ix_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0);
           (34%nat, mkAF IX_NM_LO (IX_NM_LO + 632) 3); (35%nat, mkAF IX_IX_LO (IX_IX_LO + 316) 2);
           (33%nat, mkAF 1 80 0); (37%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] [].
Definition ix_ss (AF : Z) : sstate := mkSS (AF + 0x70) ix_sr [ix_frame; ix_nmr; ix_ixr] None ix_facts.

Definition ix_extra (regs : bvmap 5 word) (n i p iv : Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 (n - i); Z_to_bv 64 (IX_NM_LO + 8 * i); Z_to_bv 64 (IX_IX_LO + 4 * i);
   Z_to_bv 64 p; Z_to_bv 64 iv;
   getr regs 1; getr regs 5; getr regs 6; getr regs 7;
   getr regs 10; getr regs 11; getr regs 12; getr regs 13;
   getr regs 14; getr regs 15; getr regs 16; getr regs 17;
   getr regs 28; getr regs 29; getr regs 30; getr regs 31].

(* the registers at the loop head, for the turn with index i *)
Definition ix_inv (regs_e regs : bvmap 5 word) (n i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (spZ regs_e - 80) /\
  getr regs 3 = getr regs_e 3 /\ getr regs 4 = getr regs_e 4 /\
  getr regs 8 = getr regs_e 10 /\
  getr regs 9 = Z_to_bv 64 (IX_IX_LO + 4 * i) /\
  getr regs 18 = Z_to_bv 64 (IX_NM_LO + 8 * i) /\
  getr regs 19 = Z_to_bv 64 (n - i) /\
  getr regs 20 = Z_to_bv 64 (IX_IX_LO + 4 * i) /\
  getr regs 21 = Z_to_bv 64 SB /\
  getr regs 22 = Z_to_bv 64 (IX_NM_LO + 8 * i) /\
  getr regs 23 = Z_to_bv 64 (SB + (IX_NM_LO + 8 * i) / 8) /\
  getr regs 24 = getr regs_e 24 /\ getr regs 25 = getr regs_e 25 /\
  getr regs 26 = getr regs_e 26 /\ getr regs 27 = getr regs_e 27.

(* ==========================================================================
   4. The walk
   ========================================================================== *)

Ltac ix_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ exfalso; lia
      | lazymatch type of Ha with context [ew _ 2%nat] =>
          match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ => rewrite U in Ha end;
          left; split; [left; lia | lia] end ]
    | ]);
  apply awr_ok_x_nil.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis STRCMP : AStrcmpDef.astrcmp_realizes SEGS B (pa_sigma LS___interceptor_trampoline_strcmp).

Lemma ix_vals : VAL (A_OBJ 1) = LA_GOT_SHADOW /\ VAL (A_OBJ 2) = LA_G_NL /\
  VAL (A_OBJ 64) = LA_SHADOW_CELL /\ BASE = link_text.
Proof.
  split; [rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 2) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity | exact (lv_text LV)].
Qed.

(* ---- views and the facts that travel with them ---- *)

Lemma ix_grow : forall (H : word -> bool) (m m' : word -> option byte),
  mem_grows (mrestrict H m) (mrestrict H m') -> forall a, apresent H m a -> apresent H m' a.
Proof.
  intros H m m' HG a (Hh & b & Hb). split; [exact Hh|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity].
Qed.

Lemma ix_cstr_frame : forall (m m' : word -> option byte) x s,
  acstr_at SEGS m x s ->
  (forall a, x <= a <= x + Z.of_nat (length s) -> mbyte SEGS m' a = mbyte SEGS m a) ->
  acstr_at SEGS m' x s.
Proof.
  intros m m' x s ((H0 & Hl & Hb) & Hn) HK. split; [|exact Hn]. split; [exact H0|]. split; [exact Hl|].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (HK (x + Z.of_nat i) ltac:(lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

Lemma ix_val_frame : forall (m m' : word -> option byte) a (n : nat) v,
  val_mem SEGS m a n v -> (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) ->
  val_mem SEGS m' a n v.
Proof. intros m m' a n v HV HK j Hj. rewrite (HK (a + Z.of_nat j) ltac:(lia)). exact (HV j Hj). Qed.

Lemma ix_ra_sub : forall (rd : reader) a n a' n',
  range_addressable rd SHADOW_OFF a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  range_addressable rd SHADOW_OFF a' n'.
Proof. intros rd a n a' n' H H1 H2 H3 x Hx. apply H. lia. Qed.

Lemma ix_hull_sub : forall (rd : reader) a n n',
  shadow_hull_vis rd a n -> 1 <= n' -> n' <= n ->
  shadow_hull_vis rd a n'.
Proof.
  intros rd a n n' H H1 H2 s Hs. apply H.
  pose proof (shadow_mono (a + n' - 1) (a + n - 1) ltac:(lia)) as Hm.
  unfold shadow_addr in *. split; [lia|].
  pose proof (Z.div_le_mono (SHADOW_OFF + (a + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma ix_hull_frame : forall (rd rd' : reader) a n,
  shadow_hull_vis rd a n ->
  (forall s, rd' s = rd s) -> shadow_hull_vis rd' a n.
Proof. intros rd rd' a n H HK s Hs. rewrite HK. exact (H s Hs). Qed.

Lemma ix_src_ok : forall (W : world SEGS) rgs (m : word -> option byte) x s kk,
  acstr_at SEGS (rdW W m) x s -> 0 <= kk <= Z.of_nat (length s) ->
  (forall a, x <= a < x + (kk + 1) -> ~ (spZ rgs - ESTACK <= a < spZ rgs)) ->
  src_ok SEGS W rgs m x (kk + 1).
Proof.
  intros W rgs m x s kk ((_ & _ & Hb) & _) Hkk Hsep a Ha. split; [|exact (Hsep a Ha)].
  assert (Hi : (Z.to_nat (a - x) < length (s ++ [zb 0]))%nat)
    by (rewrite length_app; cbn [length]; lia).
  pose proof (Hb (Z.to_nat (a - x)) Hi) as Hby.
  replace (x + Z.of_nat (Z.to_nat (a - x))) with a in Hby by lia.
  unfold aview. rewrite Hby.
  destruct (nth_error (s ++ [zb 0]) (Z.to_nat (a - x))) as [b|] eqn:E; [discriminate|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* ---- uniqueness: the Post speaks of any list the Pre's views give ---- *)

Lemma ix_val_unique : forall (m : word -> option byte) a (n : nat) v1 v2,
  val_mem SEGS m a n v1 -> val_mem SEGS m a n v2 ->
  0 <= v1 < 2 ^ (8 * Z.of_nat n) -> 0 <= v2 < 2 ^ (8 * Z.of_nat n) -> v1 = v2.
Proof.
  intros m a n v1 v2 H1 H2 R1 R2.
  rewrite <- (lw_bytes_of_vals n (abytes_of SEGS m a n) v1 (abytes_of_length SEGS m a n) R1
    ltac:(intros k Hk; exact (abytes_of_val SEGS m a n 0 n v1 k ltac:(cbn; lia) ltac:(lia) Hk
            ltac:(rewrite Z.add_0_r; exact H1)))).
  rewrite <- (lw_bytes_of_vals n (abytes_of SEGS m a n) v2 (abytes_of_length SEGS m a n) R2
    ltac:(intros k Hk; exact (abytes_of_val SEGS m a n 0 n v2 k ltac:(cbn; lia) ltac:(lia) Hk
            ltac:(rewrite Z.add_0_r; exact H2)))).
  reflexivity.
Qed.

Lemma ix_cstr_unique : forall (m : word -> option byte) x s1 s2,
  acstr_at SEGS m x s1 -> acstr_at SEGS m x s2 -> s1 = s2.
Proof.
  intros m x s1 s2 ((_ & _ & Ha1) & N1) ((_ & _ & Ha2) & N2).
  assert (AG : forall i, (i < length (s1 ++ [zb 0]))%nat -> (i < length (s2 ++ [zb 0]))%nat ->
    nth_error (s1 ++ [zb 0]) i = nth_error (s2 ++ [zb 0]) i)
    by (intros i Hi1 Hi2; rewrite <- (Ha1 i Hi1), <- (Ha2 i Hi2); reflexivity).
  assert (HL : length s1 = length s2).
  { destruct (Nat.lt_trichotomy (length s1) (length s2)) as [H|[H|H]]; [exfalso| exact H |exfalso].
    - pose proof (AG (length s1) ltac:(rewrite length_app; cbn [length]; lia)
                      ltac:(rewrite length_app; cbn [length]; lia)) as Hq.
      rewrite lws_nth_nul, nth_error_app1 in Hq by lia.
      apply N2. apply (nth_error_In _ (length s1)). symmetry. exact Hq.
    - pose proof (AG (length s2) ltac:(rewrite length_app; cbn [length]; lia)
                      ltac:(rewrite length_app; cbn [length]; lia)) as Hq.
      rewrite lws_nth_nul, nth_error_app1 in Hq by lia.
      apply N1. apply (nth_error_In _ (length s2)). exact Hq. }
  assert (HE : s1 ++ [zb 0] = s2 ++ [zb 0]).
  { apply ix_list_ext; [rewrite !length_app; lia|].
    intros k Hk. apply AG; rewrite length_app in Hk |- *; cbn [length] in Hk |- *; lia. }
  exact (app_inv_tail _ _ _ HE).
Qed.

Lemma ix_iftab_unique : forall (m : word -> option byte) bs t1 t2,
  aiftab_at SEGS m LA_G_NL bs t1 -> aiftab_at SEGS m LA_G_NL bs t2 -> t1 = t2.
Proof.
  intros m bs t1 t2 (L1 & _ & H1) (L2 & _ & H2).
  assert (HL : length t1 = length t2) by lia.
  apply ix_list_ext; [exact HL|]. intros kk Hk.
  destruct (ix_nth_some _ t1 kk Hk) as ([n1 i1] & E1).
  destruct (ix_nth_some _ t2 kk ltac:(lia)) as ([n2 i2] & E2).
  rewrite E1, E2. f_equal.
  destruct (H1 kk n1 i1 E1) as (Ri1 & p1 & V1 & _ & C1 & X1).
  destruct (H2 kk n2 i2 E2) as (Ri2 & p2 & V2 & _ & C2 & X2).
  assert (Hp1 : 0 <= p1 < 2 ^ 64)
    by (destruct C1 as ((Hq & Hl & _) & _); rewrite length_app in Hl; cbn [length] in Hl; lia).
  assert (Hp2 : 0 <= p2 < 2 ^ 64)
    by (destruct C2 as ((Hq & Hl & _) & _); rewrite length_app in Hl; cbn [length] in Hl; lia).
  assert (Hpe : p1 = p2)
    by (apply (ix_val_unique m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat kk) 8 p1 p2 V1 V2);
        change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
  subst p2.
  assert (Hne : n1 = n2) by exact (ix_cstr_unique m p1 n1 n2 C1 C2).
  assert (Hie : i1 = i2)
    by (apply (ix_val_unique m (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat kk) 4 i1 i2 X1 X2);
        change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
  rewrite Hne, Hie. reflexivity.
Qed.

(* ---- the nine saved registers, and the two symbolic states ---- *)

Definition ix_saved (W : world SEGS) (mem : word -> option byte) (regs_e : bvmap 5 word) : Prop :=
  val_mem SEGS (rdW W mem) (spZ regs_e - 72) 8 (bv_unsigned (getr regs_e 23)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 64) 8 (bv_unsigned (getr regs_e 22)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 56) 8 (bv_unsigned (getr regs_e 21)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 48) 8 (bv_unsigned (getr regs_e 20)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 40) 8 (bv_unsigned (getr regs_e 19)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 32) 8 (bv_unsigned (getr regs_e 18)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 24) 8 (bv_unsigned (getr regs_e 9)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 16) 8 (bv_unsigned (getr regs_e 8)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 8) 8 (bv_unsigned (getr regs_e 1)).

Definition ix_E (regs_e regs : bvmap 5 word) (n i p iv : Z) : env :=
  Eimg (Ereg regs_e (ix_extra regs n i p iv)).

Lemma ix_E_reg : forall regs_e regs n i p iv m (r : bv 5), Z.of_nat m = bv_unsigned r -> (m < 32)%nat ->
  ew (ix_E regs_e regs n i p iv) m = getr regs_e r.
Proof.
  intros regs_e regs n i p iv m r Hm Hlt. unfold ix_E.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs_e _ m r Hm).
Qed.

Lemma ix_E_ext : forall regs_e regs n i p iv j, (j < 22)%nat ->
  ew (ix_E regs_e regs n i p iv) (32 + j) = nth j (ix_extra regs n i p iv) (Z_to_bv 64 0).
Proof.
  intros regs_e regs n i p iv j Hj. unfold ix_E.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs_e _ j).
Qed.

(* the same, indexed by the atom itself, so a rewrite matches the run's `SOff a 0` *)
Lemma ix_E_at : forall regs_e regs n i p iv (a : nat), (32 <= a < 54)%nat ->
  ew (ix_E regs_e regs n i p iv) a = nth (a - 32) (ix_extra regs n i p iv) (Z_to_bv 64 0).
Proof.
  intros regs_e regs n i p iv a Ha.
  replace a with (32 + (a - 32))%nat at 1 by lia.
  apply ix_E_ext. lia.
Qed.

Lemma ix_shok : forall (E : env) (W : world SEGS) (mem : word -> option byte) a1 a2,
  ew E 32 = Z_to_bv 64 SB -> ew E 34 = Z_to_bv 64 a1 -> ew E 35 = Z_to_bv 64 a2 ->
  IX_NM_LO <= a1 -> a1 + 8 <= IX_NM_LO + 640 -> IX_IX_LO <= a2 -> a2 + 4 <= IX_IX_LO + 320 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a1 8 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a2 4 ->
  sh_ok SEGS (SOff 32 0) ix_SH E (rdW W mem).
Proof.
  intros E W mem a1 a2 X32 X34 X35 H1 H2 H3 H4 RA1 RA2.
  assert (HNMb : IX_NM_LO = 6417776) by reflexivity.
  assert (HIXb : IX_IX_LO = 6418416) by reflexivity.
  assert (HSBb : SB = 2147450880) by reflexivity.
  unfold sh_ok, ix_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    unfold shent_ok, app_apart; cbn [she_m she_lo she_hi].
  - rewrite (U_atom E 32 SB X32 ltac:(lia)), (U_atom E 34 a1 X34 ltac:(lia)).
    split; [rewrite Z.add_0_r; rewrite <- (aview_rd_of SEGS); exact RA1|].
    intros a Ha. cbn in Ha. lia.
  - rewrite (U_atom E 32 SB X32 ltac:(lia)), (U_atom E 35 a2 X35 ltac:(lia)).
    split; [rewrite Z.add_0_r; rewrite <- (aview_rd_of SEGS); exact RA2|].
    intros a Ha. cbn in Ha. lia.
Qed.

Lemma ix_seat : forall AF G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k
    (regs_e regs : bvmap 5 word) n i p iv,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs_e mod 16 = 0 -> sp0 - STK <= spZ regs_e - FUZZ_IF_NAMETOINDEX_AK -> spZ regs_e <= sp0 ->
  ix_inv regs_e regs n i -> ix_saved W mem regs_e ->
  0 <= i -> i + 1 <= n -> n <= 80 ->
  0 <= p < 2 ^ 64 -> 0 <= iv < 2 ^ 31 ->
  val_mem SEGS (rdW W mem) (IX_NM_LO + 8 * i) 8 p ->
  val_mem SEGS (rdW W mem) (IX_IX_LO + 4 * i) 4 iv ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (IX_NM_LO + 8 * i) 8 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (IX_IX_LO + 4 * i) 4 ->
  st_ok_pi SEGS VAL (ix_E regs_e regs n i p iv) (ix_ss AF)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF + 0x70))) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 32 0) ix_SH (ix_E regs_e regs n i p iv) (rdW W mem).
Proof.
intros AF G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs_e regs n i p iv
  HJ H16 Hwlo Hwhi HINV HSV Hi0 Hin Hn80 Hp Hiv Vp Viv RAn RAi.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HK : FUZZ_IF_NAMETOINDEX_AK = 8272) by reflexivity.
assert (Hsp46 : 2 ^ 46 <= spZ regs_e <= 2 ^ 47) by lia.
destruct HINV as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
destruct HSV as (S7 & S6 & S5 & S4 & S3 & S2 & S1 & S0 & SRA).
set (E := ix_E regs_e regs n i p iv).
assert (HNMb : IX_NM_LO = 6417776) by reflexivity.
assert (HIXb : IX_IX_LO = 6418416) by reflexivity.
assert (HSBb : SB = 2147450880) by reflexivity.
assert (E1 : ew E 1 = getr regs_e 1) by (apply (ix_E_reg _ _ _ _ _ _ 1%nat 1%bv); [reflexivity | lia]).
assert (E2 : ew E 2 = getr regs_e 2) by (apply (ix_E_reg _ _ _ _ _ _ 2%nat 2%bv); [reflexivity | lia]).
assert (E8 : ew E 8 = getr regs_e 8) by (apply (ix_E_reg _ _ _ _ _ _ 8%nat 8%bv); [reflexivity | lia]).
assert (E9 : ew E 9 = getr regs_e 9) by (apply (ix_E_reg _ _ _ _ _ _ 9%nat 9%bv); [reflexivity | lia]).
assert (E18 : ew E 18 = getr regs_e 18) by (apply (ix_E_reg _ _ _ _ _ _ 18%nat 18%bv); [reflexivity | lia]).
assert (E19 : ew E 19 = getr regs_e 19) by (apply (ix_E_reg _ _ _ _ _ _ 19%nat 19%bv); [reflexivity | lia]).
assert (E20 : ew E 20 = getr regs_e 20) by (apply (ix_E_reg _ _ _ _ _ _ 20%nat 20%bv); [reflexivity | lia]).
assert (E21 : ew E 21 = getr regs_e 21) by (apply (ix_E_reg _ _ _ _ _ _ 21%nat 21%bv); [reflexivity | lia]).
assert (E22 : ew E 22 = getr regs_e 22) by (apply (ix_E_reg _ _ _ _ _ _ 22%nat 22%bv); [reflexivity | lia]).
assert (E23 : ew E 23 = getr regs_e 23) by (apply (ix_E_reg _ _ _ _ _ _ 23%nat 23%bv); [reflexivity | lia]).
assert (X32 : ew E 32 = Z_to_bv 64 SB) by exact (ix_E_ext _ _ _ _ _ _ 0%nat ltac:(lia)).
assert (X33 : ew E 33 = Z_to_bv 64 (n - i)) by exact (ix_E_ext _ _ _ _ _ _ 1%nat ltac:(lia)).
assert (X34 : ew E 34 = Z_to_bv 64 (IX_NM_LO + 8 * i)) by exact (ix_E_ext _ _ _ _ _ _ 2%nat ltac:(lia)).
assert (X35 : ew E 35 = Z_to_bv 64 (IX_IX_LO + 4 * i)) by exact (ix_E_ext _ _ _ _ _ _ 3%nat ltac:(lia)).
assert (X36 : ew E 36 = Z_to_bv 64 p) by exact (ix_E_ext _ _ _ _ _ _ 4%nat ltac:(lia)).
assert (X37 : ew E 37 = Z_to_bv 64 iv) by exact (ix_E_ext _ _ _ _ _ _ 5%nat ltac:(lia)).
assert (E3 : ew E 3 = getr regs_e 3) by (apply (ix_E_reg _ _ _ _ _ _ 3%nat 3%bv); [reflexivity | lia]).
assert (E4 : ew E 4 = getr regs_e 4) by (apply (ix_E_reg _ _ _ _ _ _ 4%nat 4%bv); [reflexivity | lia]).
assert (E10 : ew E 10 = getr regs_e 10) by (apply (ix_E_reg _ _ _ _ _ _ 10%nat 10%bv); [reflexivity | lia]).
assert (E24 : ew E 24 = getr regs_e 24) by (apply (ix_E_reg _ _ _ _ _ _ 24%nat 24%bv); [reflexivity | lia]).
assert (E25 : ew E 25 = getr regs_e 25) by (apply (ix_E_reg _ _ _ _ _ _ 25%nat 25%bv); [reflexivity | lia]).
assert (E26 : ew E 26 = getr regs_e 26) by (apply (ix_E_reg _ _ _ _ _ _ 26%nat 26%bv); [reflexivity | lia]).
assert (E27 : ew E 27 = getr regs_e 27) by (apply (ix_E_reg _ _ _ _ _ _ 27%nat 27%bv); [reflexivity | lia]).
assert (X38 : ew E 38 = getr regs 1) by exact (ix_E_ext _ _ _ _ _ _ 6%nat ltac:(lia)).
assert (X39 : ew E 39 = getr regs 5) by exact (ix_E_ext _ _ _ _ _ _ 7%nat ltac:(lia)).
assert (X40 : ew E 40 = getr regs 6) by exact (ix_E_ext _ _ _ _ _ _ 8%nat ltac:(lia)).
assert (X41 : ew E 41 = getr regs 7) by exact (ix_E_ext _ _ _ _ _ _ 9%nat ltac:(lia)).
assert (X42 : ew E 42 = getr regs 10) by exact (ix_E_ext _ _ _ _ _ _ 10%nat ltac:(lia)).
assert (X43 : ew E 43 = getr regs 11) by exact (ix_E_ext _ _ _ _ _ _ 11%nat ltac:(lia)).
assert (X44 : ew E 44 = getr regs 12) by exact (ix_E_ext _ _ _ _ _ _ 12%nat ltac:(lia)).
assert (X45 : ew E 45 = getr regs 13) by exact (ix_E_ext _ _ _ _ _ _ 13%nat ltac:(lia)).
assert (X46 : ew E 46 = getr regs 14) by exact (ix_E_ext _ _ _ _ _ _ 14%nat ltac:(lia)).
assert (X47 : ew E 47 = getr regs 15) by exact (ix_E_ext _ _ _ _ _ _ 15%nat ltac:(lia)).
assert (X48 : ew E 48 = getr regs 16) by exact (ix_E_ext _ _ _ _ _ _ 16%nat ltac:(lia)).
assert (X49 : ew E 49 = getr regs 17) by exact (ix_E_ext _ _ _ _ _ _ 17%nat ltac:(lia)).
assert (X50 : ew E 50 = getr regs 28) by exact (ix_E_ext _ _ _ _ _ _ 18%nat ltac:(lia)).
assert (X51 : ew E 51 = getr regs 29) by exact (ix_E_ext _ _ _ _ _ _ 19%nat ltac:(lia)).
assert (X52 : ew E 52 = getr regs 30) by exact (ix_E_ext _ _ _ _ _ _ 20%nat ltac:(lia)).
assert (X53 : ew E 53 = getr regs 31) by exact (ix_E_ext _ _ _ _ _ _ 21%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs_e) by (rewrite E2; reflexivity).
assert (U34 : bv_unsigned (ew E 34) = IX_NM_LO + 8 * i) by (rewrite X34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = IX_IX_LO + 4 * i) by (rewrite X35; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ix_ss. apply pa_entry_st_ok_full.
  + apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<- | Hr]); [..|destruct Hr];
      (* name the register's symbolic value, then read it off the environment *)
      [ lazymatch goal with |- _ = sv_denot ?EE (sr_get ?L ?R) =>
          let v := eval vm_compute in (sr_get L R) in change (sr_get L R) with v end .. ];
      [ rewrite getr_zero; reflexivity
      | rewrite ix_soff0, X38; reflexivity
      | rewrite (ix_soffc E 2 (-80) (spZ regs_e));
          [exact R2 | rewrite E2; symmetry; apply Z_to_bv_bv_unsigned | lia | lia]
      | rewrite ix_soff0, E3; exact R3
      | rewrite ix_soff0, E4; exact R4
      | rewrite ix_soff0, X39; reflexivity
      | rewrite ix_soff0, X40; reflexivity
      | rewrite ix_soff0, X41; reflexivity
      | rewrite ix_soff0, E10; exact R8
      | rewrite ix_soff0, X35; exact R9
      | rewrite ix_soff0, X42; reflexivity
      | rewrite ix_soff0, X43; reflexivity
      | rewrite ix_soff0, X44; reflexivity
      | rewrite ix_soff0, X45; reflexivity
      | rewrite ix_soff0, X46; reflexivity
      | rewrite ix_soff0, X47; reflexivity
      | rewrite ix_soff0, X48; reflexivity
      | rewrite ix_soff0, X49; reflexivity
      | rewrite ix_soff0, X34; exact R18
      | rewrite ix_soff0, X33; exact R19
      | rewrite ix_soff0, X35; exact R20
      | rewrite ix_soff0, X32; exact R21
      | rewrite ix_soff0, X34; exact R22
      | rewrite (ix_denot_shx E 34 (IX_NM_LO + 8 * i) SB X34 X32 ltac:(lia) ltac:(lia)); exact R23
      | rewrite ix_soff0, E24; exact R24
      | rewrite ix_soff0, E25; exact R25
      | rewrite ix_soff0, E26; exact R26
      | rewrite ix_soff0, E27; exact R27
      | rewrite ix_soff0, X50; reflexivity
      | rewrite ix_soff0, X51; reflexivity
      | rewrite ix_soff0, X52; reflexivity
      | rewrite ix_soff0, X53; reflexivity ].
  + vm_compute. reflexivity.
  + unfold ix_frame, ix_nmr, ix_ixr.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [ms_mem restrict mkst];
        [ apply (chunk_ok_val SEGS E _ (spZ regs_e) (-72) 8 (SOff 23 0) (bv_unsigned (getr regs_e 23)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-64) 8 (SOff 22 0) (bv_unsigned (getr regs_e 22)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-56) 8 (SOff 21 0) (bv_unsigned (getr regs_e 21)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-48) 8 (SOff 20 0) (bv_unsigned (getr regs_e 20)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-40) 8 (SOff 19 0) (bv_unsigned (getr regs_e 19)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-32) 8 (SOff 18 0) (bv_unsigned (getr regs_e 18)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-24) 8 (SOff 9 0) (bv_unsigned (getr regs_e 9)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-16) 8 (SOff 8 0) (bv_unsigned (getr regs_e 8)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-8) 8 (SOff 1 0) (bv_unsigned (getr regs_e 1))) ];
        try (rewrite ix_soff0; first [rewrite E23 | rewrite E22 | rewrite E21 | rewrite E20 | rewrite E19
                                     | rewrite E18 | rewrite E9 | rewrite E8 | rewrite E1];
             symmetry; apply Z_to_bv_bv_unsigned);
        try (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range);
        try (cbn; lia);
        first [exact S7 | exact S6 | exact S5 | exact S4 | exact S3 | exact S2 | exact S1 | exact S0 | exact SRA].
    * cbn [base_val]. fold E. rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (IX_NM_LO + 8 * i) 0 8 (SOff 36 0) p);
        [rewrite ix_soff0, X36; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. cbn [ms_mem restrict mkst]. exact Vp.
    * cbn [base_val]. fold E. rewrite U35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (IX_IX_LO + 4 * i) 0 4 (SOff 37 0) iv);
        [rewrite ix_soff0, X37; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
      rewrite Z.add_0_r. cbn [ms_mem restrict mkst]. exact Viv.
  + apply pairwise_disjoint_of_extents.
    unfold ix_frame, ix_nmr, ix_ixr, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. fold E.
    cbn [base_val]. rewrite Usp, U34, U35.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [ix_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, X32, X34, X35, X33, X37.
    rewrite !unsigned_lit_small by lia.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- apply (ix_shok E W mem (IX_NM_LO + 8 * i) (IX_IX_LO + 4 * i) X32 X34 X35);
    solve [lia | exact RAn | exact RAi].
Qed.

Lemma ix_entry : forall AF clo chi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs : bvmap 5 word) bs,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - FUZZ_IF_NAMETOINDEX_AK -> spZ regs <= sp0 ->
  anlk_at SEGS (rdW W memc) LA_G_NL bs ->
  0 <= clo -> clo <= nk_n_if bs <= chi -> chi < 2 ^ 31 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (ix_e_extra (nk_n_if bs)))) (ix_e_ss AF clo chi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF)) memc (seg_rom SEGS))).
Proof.
intros AF clo chi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs
  HJ H16 Hwlo Hwhi HNK Hclo Hmid Hchi.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HK : FUZZ_IF_NAMETOINDEX_AK = 8272) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
destruct ix_vals as (V1 & V2 & V64 & VB).
rewrite V1, V64 in Kgot. rewrite V64 in Kcell.
pose proof HNK as [[Hab Hwr] HL].
set (E := Eimg (Ereg regs (ix_e_extra (nk_n_if bs)))).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (ix_e_extra (nk_n_if bs))) m)
  by (intros m Hm; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2%nat 2%bv eq_refl)).
assert (X32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0%nat)).
assert (X33 : ew E 33 = Z_to_bv 64 (nk_n_if bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1%nat)).
assert (Eg : ew E (A_OBJ 2) = Z_to_bv 64 LA_G_NL)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V2; reflexivity).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 LA_GOT_SHADOW)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V1; reflexivity).
assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 LA_SHADOW_CELL)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V64; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VBv : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v)
  by (intros m v Hm Hv; cbn [base_val]; rewrite Hm; apply unsigned_lit_small; exact Hv).
rewrite restrict_mkst_fx. unfold ix_e_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ix_e_regions, stack_region, got_regionP, bcell_regionP, ix_nif_region, IX_FRAME.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. cbn [ms_mem restrict mkst]. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VBv _ _ Egot) by (unfold LA_GOT_SHADOW; lia).
    split; [unfold LA_GOT_SHADOW; lia|]. split; [unfold LA_GOT_SHADOW; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_GOT_SHADOW 0 8 (SOff (A_OBJ 64) 0) LA_SHADOW_CELL);
      [rewrite ix_soff0, Ecell; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold LA_SHADOW_CELL; lia | cbn; lia |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst]. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VBv _ _ Ecell) by (unfold LA_SHADOW_CELL; lia).
    split; [unfold LA_SHADOW_CELL; lia|]. split; [unfold LA_SHADOW_CELL; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_SHADOW_CELL 0 8 (SOff 32 0) SB);
      [rewrite ix_soff0, X32; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst]. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_NL; lia).
    split; [unfold LA_G_NL, NK_N_IF; lia|]. split; [unfold LA_G_NL, NK_N_IF; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_G_NL NK_N_IF 4 (SOff 33 0) (nk_n_if bs));
      [rewrite ix_soff0, X33; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
    cbn [ms_mem restrict mkst].
    unfold nk_n_if, fld_u32. change 4%nat with (N.to_nat 4).
    exact (anlk_field SEGS (rdW W memc) LA_G_NL bs NK_N_IF (N.to_nat 4) HNK ltac:(unfold NK_N_IF; lia)
             ltac:(unfold NK_N_IF, NK_SIZE; cbn; lia)).
- apply pairwise_disjoint_of_extents.
  unfold ix_e_regions, stack_region, got_regionP, bcell_regionP, ix_nif_region, extent_of_region, IX_FRAME.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. fold E.
  rewrite (VBv _ _ Egot) by (unfold LA_GOT_SHADOW; lia).
  rewrite (VBv _ _ Ecell) by (unfold LA_SHADOW_CELL; lia).
  rewrite (VBv _ _ Eg) by (unfold LA_G_NL; lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold LA_G_NL, LA_GOT_SHADOW, LA_SHADOW_CELL, NK_N_IF.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [ix_e_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, Eg, X32, X33.
  rewrite !unsigned_lit_small by (unfold SB, LA_G_NL; lia).
  rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 4) with 16. unfold SB, LA_G_NL.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ---- the Post, from the register the run leaves in a0 ---- *)
Lemma ix_post_of : forall (regs regs2 : bvmap 5 word) (m m2 : word -> option byte) bs tab nm,
  anlk_at SEGS m LA_G_NL bs -> aiftab_at SEGS m LA_G_NL bs tab -> acstr_at SEGS m (aarg regs 0) nm ->
  getr regs2 10 = w64 (index_of tab nm) ->
  fuzz_if_nametoindex_apost SEGS regs m regs2 m2.
Proof.
  intros regs regs2 m m2 bs tab nm HNK HTAB HCS Hres.
  unfold fuzz_if_nametoindex_apost. intros bs0 tab0 nm0 H1 H2 H3.
  rewrite (anlk_at_unique SEGS m LA_G_NL bs0 bs H1 HNK) in H2.
  rewrite (ix_iftab_unique m bs tab0 tab H2 HTAB).
  rewrite (ix_cstr_unique m (aarg regs 0) nm0 nm H3 HCS).
  exact Hres.
Qed.

(* ---- the facts of one turn, read off the Pre at the turn's two memories ---- *)

(* the part of the contract's astrcmp_arg_ni the walk moves from one memory to the next: the wrapper's
   contract (AStrcmpDef) reads no tail byte, so the Pre's tail conjunct never has to travel *)
Definition ix_argf (rgs : bvmap 5 word) (m : word -> option byte) (x : Z) (s : list byte) : Prop :=
  0 < x /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ amem_range x (Z.of_nat (length s) + 1) /\
  range_addressable (ard SEGS m) SHADOW_OFF x (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (ard SEGS m) x (Z.of_nat (length s) + 1) /\
  apart_frame rgs FUZZ_IF_NAMETOINDEX_AK x (Z.of_nat (length s) + 1).

Lemma ix_argf_of : forall rgs m x s,
  astrcmp_arg_ni SEGS rgs FUZZ_IF_NAMETOINDEX_AK m x s -> ix_argf rgs m x s.
Proof. intros rgs m x s (H1 & H2 & H3 & H4 & H5 & H6 & _). repeat split; assumption. Qed.

Lemma ix_shadow_low : forall x, 0 <= x < kHighMemEnd -> 0 <= shadow_addr x < alloc_ceiling.
Proof.
  intros x Hx. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (shadow_addr_bounds x Hx) as Hsb. unfold kHighShadowEnd in Hsb. lia.
Qed.

Lemma ix_shadow_low8 : forall x, 0 <= x < kHighMemEnd -> 0 <= shadow_addr x /\ shadow_addr x + 8 < alloc_ceiling.
Proof.
  intros x Hx. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (shadow_addr_bounds x Hx) as Hsb. unfold kHighShadowEnd in Hsb. lia.
Qed.

Lemma ix_arg_frame : forall (W : world SEGS) (rgs : bvmap 5 word) (m m' : word -> option byte) x s,
  ix_argf rgs (rdW W m) x s ->
  alloc_ceiling <= spZ rgs - FUZZ_IF_NAMETOINDEX_AK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rgs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ rgs) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  ix_argf rgs (rdW W m') x s.
Proof.
  intros W rgs m m' x s (H1 & H2 & H3 & H4 & H5 & H6) Hceil UN.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HSH : forall y, x <= y < x + (Z.of_nat (length s) + 1) ->
    aview SEGS (w_H W) m' (shadow_addr y) = aview SEGS (w_H W) m (shadow_addr y)).
  { intros y Hy. pose proof (ix_shadow_low y ltac:(unfold amem_range, kHighMemBeg, kLowMemEnd in H3; lia)) as Hs.
    apply UN; lia. }
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply (ra_shadow_eq (ard SEGS (rdW W m))); [exact H4 | exact HSH]|].
  split; [|exact H6].
  intros sadr Hsadr.
  assert (Hlo : 0 <= shadow_addr x /\ shadow_addr x + 8 < alloc_ceiling)
    by (apply ix_shadow_low8; unfold amem_range, kHighMemBeg, kLowMemEnd in H3; lia).
  assert (Hhi : 0 <= shadow_addr (x + (Z.of_nat (length s) + 1) - 1) /\
                shadow_addr (x + (Z.of_nat (length s) + 1) - 1) + 8 < alloc_ceiling)
    by (apply ix_shadow_low8; unfold amem_range, kHighMemBeg, kLowMemEnd in H3; lia).
  pose proof (Z_div_mod_eq_full (shadow_addr x) 8) as D1.
  pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)) as M1.
  pose proof (Z_div_mod_eq_full (shadow_addr (x + (Z.of_nat (length s) + 1) - 1)) 8) as D2.
  pose proof (Z.mod_pos_bound (shadow_addr (x + (Z.of_nat (length s) + 1) - 1)) 8 ltac:(lia)) as M2.
  assert (HEq : ard SEGS (rdW W m') sadr = ard SEGS (rdW W m) sadr)
    by exact (UN sadr ltac:(lia) ltac:(lia)).
  rewrite HEq. exact (H5 sadr Hsadr).
Qed.

Lemma ix_cstr_frame_sep : forall (W : world SEGS) (rgs : bvmap 5 word) (m m' : word -> option byte) x s,
  acstr_at SEGS (rdW W m) x s ->
  apart_frame rgs FUZZ_IF_NAMETOINDEX_AK x (Z.of_nat (length s) + 1) ->
  amem_range x (Z.of_nat (length s) + 1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rgs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ rgs) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  acstr_at SEGS (rdW W m') x s.
Proof.
  intros W rgs m m' x s HC Hpart Hmem UN.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as ((Hx0 & Hxl & _) & _).
  rewrite length_app in Hxl. cbn [length] in Hxl.
  apply (ix_cstr_frame (rdW W m)); [exact HC|].
  intros a Ha. apply (mbyte_of_aview SEGS).
  unfold apart_frame in Hpart.
  apply UN; destruct Hpart as [Hp|Hp]; lia.
Qed.

Lemma ix_turn_prep : forall (W : world SEGS) (regs : bvmap 5 word) (memc m m2 : word -> option byte)
    bs tab nm i,
  aiftab_at SEGS (rdW W memc) LA_G_NL bs tab ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (LA_G_NL + NK_IF_NAME) (8 * Z.of_nat (length tab)) ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (LA_G_NL + NK_IF_INDEX) (4 * Z.of_nat (length tab)) ->
  acstr_at SEGS (rdW W memc) (aarg regs 0) nm ->
  astrcmp_arg_ni SEGS regs FUZZ_IF_NAMETOINDEX_AK (rdW W memc) (aarg regs 0) nm ->
  (forall j n2 iv q, nth_error tab j = Some (n2, iv) ->
     au64_at SEGS (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat j) q -> 0 <= q < 2 ^ 64 ->
     astrcmp_arg_ni SEGS regs FUZZ_IF_NAMETOINDEX_AK (rdW W memc) q n2) ->
  0 <= i < Z.of_nat (length tab) ->
  alloc_ceiling <= spZ regs - FUZZ_IF_NAMETOINDEX_AK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
     aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
     aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a) ->
  exists q iv n2,
    nth_error tab (Z.to_nat i) = Some (n2, iv) /\
    0 < q < 2 ^ 64 /\ 0 <= iv < 2 ^ 31 /\
    val_mem SEGS (rdW W m) (IX_NM_LO + 8 * i) 8 q /\
    val_mem SEGS (rdW W m) (IX_IX_LO + 4 * i) 4 iv /\
    range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (IX_NM_LO + 8 * i) 8 /\
    range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (IX_IX_LO + 4 * i) 4 /\
    acstr_at SEGS (rdW W m2) q n2 /\ acstr_at SEGS (rdW W m2) (aarg regs 0) nm /\
    ix_argf regs (rdW W m2) q n2 /\ ix_argf regs (rdW W m2) (aarg regs 0) nm.
Proof.
  intros W regs memc m m2 bs tab nm i (HTn & HT80 & HTe) RAN RAI HCS HARG HTARG Hi Hceil UN UN2.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HIM : forall a, 0 <= a < alloc_ceiling ->
    aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) by (intros a Ha; apply UN; lia).
  assert (HIMb : forall a, 0 <= a < alloc_ceiling ->
    mbyte SEGS (rdW W m) a = mbyte SEGS (rdW W memc) a)
    by (intros a Ha; apply (mbyte_of_aview SEGS); apply HIM; exact Ha).
  destruct (ix_nth_some _ tab (Z.to_nat i) ltac:(lia)) as ([n2 iv] & He).
  destruct (HTe (Z.to_nat i) n2 iv He) as (Hiv & q & Vq & Hq0 & HCq & Viv).
  rewrite Z2Nat.id in Vq, Viv by lia.
  assert (Hqrng : 0 <= q < 2 ^ 64).
  { destruct HCq as ((Hq1 & Hq2 & _) & _). rewrite length_app in Hq2. cbn [length] in Hq2. lia. }
  pose proof (ix_argf_of _ _ _ _
    (HTARG (Z.to_nat i) n2 iv q He ltac:(rewrite Z2Nat.id by lia; exact Vq) Hqrng)) as HAq.
  pose proof (ix_argf_of _ _ _ _ HARG) as HAn.
  pose proof HAq as (Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6).
  pose proof HAn as (Hn1 & Hn2 & Hn3 & Hn4 & Hn5 & Hn6).
  exists q, iv, n2.
  split; [exact He|]. split; [lia|]. split; [exact Hiv|].
  split.
  { apply (ix_val_frame (rdW W memc)); [unfold IX_NM_LO; exact Vq|].
    intros x Hx. apply HIMb. unfold IX_NM_LO, LA_G_NL, NK_IF_NAME in *. lia. }
  split.
  { apply (ix_val_frame (rdW W memc)); [unfold IX_IX_LO; exact Viv|].
    intros x Hx. apply HIMb. unfold IX_IX_LO, LA_G_NL, NK_IF_INDEX in *. lia. }
  split.
  { apply (ra_shadow_eq (ard SEGS (rdW W memc))).
    - apply (ix_ra_sub _ (LA_G_NL + NK_IF_NAME) (8 * Z.of_nat (length tab)));
        [exact RAN | unfold IX_NM_LO; lia | lia | unfold IX_NM_LO; lia].
    - intros x Hx. exact (HIM (shadow_addr x)
        ltac:(apply ix_shadow_low; unfold IX_NM_LO, LA_G_NL, NK_IF_NAME, kHighMemEnd in *; lia)). }
  split.
  { apply (ra_shadow_eq (ard SEGS (rdW W memc))).
    - apply (ix_ra_sub _ (LA_G_NL + NK_IF_INDEX) (4 * Z.of_nat (length tab)));
        [exact RAI | unfold IX_IX_LO; lia | lia | unfold IX_IX_LO; lia].
    - intros x Hx. exact (HIM (shadow_addr x)
        ltac:(apply ix_shadow_low; unfold IX_IX_LO, LA_G_NL, NK_IF_INDEX, kHighMemEnd in *; lia)). }
  split; [exact (ix_cstr_frame_sep W regs memc m2 q n2 HCq Hq6 Hq3 UN2)|].
  split; [exact (ix_cstr_frame_sep W regs memc m2 (aarg regs 0) nm HCS Hn6 Hn3 UN2)|].
  split; [exact (ix_arg_frame W regs memc m2 q n2 HAq Hceil UN2)
         | exact (ix_arg_frame W regs memc m2 (aarg regs 0) nm HAn Hceil UN2)].
Qed.

(* ---- the Post at any exit of the walk ---- *)
Lemma ix_exit : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regs2 : bvmap 5 word) (mem2 : word -> option byte) md2 bs tab nm,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  sp0 - STK <= spZ regs - FUZZ_IF_NAMETOINDEX_AK -> spZ regs <= sp0 ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  anlk_at SEGS (rdW W memc) LA_G_NL bs -> aiftab_at SEGS (rdW W memc) LA_G_NL bs tab ->
  acstr_at SEGS (rdW W memc) (aarg regs 0) nm ->
  getr regs2 10 = w64 (index_of tab nm) ->
  apost SK SEGS B FUZZ_IF_NAMETOINDEX_AK 0
    (fun a => inFP (fuzz_if_nametoindex_awr regs (rdW W memc)) a)
    G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (fun ly2 S2 W2 regs2' mem2' md2' =>
       S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       fuzz_if_nametoindex_apost SEGS regs (rdW W memc) regs2' (rdW W2 mem2'))
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 bs tab nm
  HJ HJ2 Hwlo Hwhi Hfd Hfs HP UN GR HNK HTAB HCS Hres.
pose proof HJ2 as (HSTK2 & HXO2 & (memS2 & HJi2 & _) & _).
pose proof HJi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HK : FUZZ_IF_NAMETOINDEX_AK = 8272) by reflexivity.
assert (HPW : forall a, spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs -> apresent (w_H W) mem2 a).
{ intros a Ha. apply Hpres2. lia. }
apply (apost_leaf SK SEGS B LAWS pa_segs_low FUZZ_IF_NAMETOINDEX_AK 0
  (fun a => inFP (fuzz_if_nametoindex_awr regs (rdW W memc)) a)
  G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 _
  HJ HJ2 ltac:(lia) Hwlo ltac:(lia) Hfd Hfs HP
  ltac:(intros a Ha Hw _; exact (UN a Ha Hw)) GR
  HPW
  ltac:(intros x Hx; unfold fuzz_if_nametoindex_awr, inFP in Hx;
        destruct Hx as (yy & Hin & _); destruct Hin)).
split; [apply ix_set_fs_id|]. split; [apply Permutation_refl|].
exact (ix_post_of regs regs2 (rdW W memc) (rdW W mem2) bs tab nm HNK HTAB HCS Hres).
Qed.

(* ---- the answer word of the wrapper at the `beqz` ---- *)
Lemma ix_res_eq : forall c1 c2, bv_unsigned (w64 (AStrcmpDef.strcmp_res c1 c2)) = 0 ->
  AStrcmpDef.strcmp_res c1 c2 = 0.
Proof.
  intros c1 c2 H.
  destruct (ix_strcmp_res_cases c1 c2) as [Eq|[Eq|Eq]]; rewrite Eq in H |- *; [reflexivity| |];
    exfalso; unfold w64 in H; rewrite Z_to_bv_unsigned in H;
    unfold bv_wrap, bv_modulus in H; change (2 ^ Z.of_N 64) with (2 ^ 64) in H.
  - assert (Hm : (-1) mod 2 ^ 64 = 2 ^ 64 - 1).
    { replace (-1) with ((2 ^ 64 - 1) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
      apply Z.mod_small. lia. }
    lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.

Lemma ix_res_ne : forall c1 c2, bv_unsigned (w64 (AStrcmpDef.strcmp_res c1 c2)) <> 0 ->
  AStrcmpDef.strcmp_res c1 c2 <> 0.
Proof.
  intros c1 c2 H Eq. apply H. rewrite Eq. unfold w64. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_0_l. lia.
Qed.

(* ---- the call of wrapper_strcmp at +0x80, in the shape the loop needs ---- *)
Lemma ix_amem_sub : forall x n n', amem_range x n -> 0 <= n' -> n' <= n -> amem_range x n'.
Proof. intros x n n' H H1 H2. unfold amem_range in *. destruct H as [H|[H H']]; [left; lia | right; split; lia]. Qed.

Lemma ix_call : forall (W : world SEGS) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdq k
    (regs rgs : bvmap 5 word) (memT : word -> option byte) q nm n2 raw,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdq k ->
  spZ rgs = spZ regs - 80 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - FUZZ_IF_NAMETOINDEX_AK -> spZ regs <= sp0 ->
  getr rgs 3 = w64 (as_gp B) -> getr rgs 4 = w64 (as_tp B) ->
  getr rgs 1 = raw -> YK0s.ret_ok raw ->
  getr rgs 10 = w64 q -> getr rgs 11 = w64 (aarg regs 0) ->
  acstr_at SEGS (rdW W memT) q n2 -> acstr_at SEGS (rdW W memT) (aarg regs 0) nm ->
  ix_argf regs (rdW W memT) q n2 -> ix_argf regs (rdW W memT) (aarg regs 0) nm ->
  SRr SEGS W
    (mkCfg (mkst rgs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_strcmp)) memT (seg_rom SEGS)) mdq)
    (fun W2 cf => W2 = W /\ exists regs2 mem2 md2,
       cf = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       same_but_materialized mdq md2 /\
       aregs_preserved rgs regs2 /\
       (getr regs2 10 = w64 0 <-> n2 = nm) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs - 80) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdq k regs rgs memT q nm n2 raw
  HGX HJ Hsp H16 Hwlo Hwhi Hgp Htp Hra Hraw H10 H11 CSq CSnm AQ AN.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : FUZZ_IF_NAMETOINDEX_AK = 8272) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof AQ as (Aq0 & Aqlen & Aqmem & Aqra & Aqhull & Aqpart).
pose proof AN as (An0 & Anlen & Anmem & Anra & Anhull & Anpart).
destruct (astrcmp_cstr_meet SEGS W memT q (aarg regs 0) n2 nm CSq CSnm)
  as (kk & cb1 & cb2 & Hkk0 & Hkk1 & Hkk2 & HMEET & HIFF).
unfold apart_frame in Aqpart, Anpart.
eapply SRr_mono.
{ apply (aj_gx_astrcmp_at SK SEGS B LAWS pa_segs_low
    (pa_sigma LS___interceptor_trampoline_strcmp) STRCMP
    G XO OUT W rgs memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdq k q (aarg regs 0) kk cb1 cb2 raw).
  - exact HGX.
  - exact HJ.
  - rewrite Hsp. replace (spZ regs - 80) with (spZ regs - 5 * 16) by lia.
    rewrite Zminus_mod, H16. reflexivity.
  - lia.
  - lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact H10.
  - exact H11.
  - exact Aq0.
  - exact An0.
  - lia.
  - unfold amem_range, kHighMemBeg, kLowMemEnd in Aqmem. lia.
  - unfold amem_range, kHighMemBeg, kLowMemEnd in Anmem. lia.
  - exact HMEET.
  - apply (ix_src_ok W rgs memT q n2 kk CSq ltac:(lia)). intros a Ha. lia.
  - apply (ix_src_ok W rgs memT (aarg regs 0) nm kk CSnm ltac:(lia)). intros a Ha. lia.
  - intros a Ha. lia.
  - intros a Ha. lia.
  - exact (ix_amem_sub q (Z.of_nat (length n2) + 1) (kk + 1) Aqmem ltac:(lia) ltac:(lia)).
  - exact (ix_amem_sub (aarg regs 0) (Z.of_nat (length nm) + 1) (kk + 1) Anmem ltac:(lia) ltac:(lia)).
  - exact (ix_ra_sub _ q (Z.of_nat (length n2) + 1) q (kk + 1) Aqra ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (ix_hull_sub _ q (Z.of_nat (length n2) + 1) (kk + 1) Aqhull ltac:(lia) ltac:(lia)).
  - exact (ix_ra_sub _ (aarg regs 0) (Z.of_nat (length nm) + 1) (aarg regs 0) (kk + 1) Anra
             ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (ix_hull_sub _ (aarg regs 0) (Z.of_nat (length nm) + 1) (kk + 1) Anhull ltac:(lia) ltac:(lia)). }
cbv beta. intros W2 cf _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hsame & HP2 & Hres & Hfr & Hpres).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hsame|]. split; [exact HP2|].
split.
{ rewrite Hres. split.
  - intros Hw. apply (proj1 HIFF). apply ix_res_eq.
    rewrite Hw. apply unsigned_lit_small. lia.
  - intros Heq. rewrite (proj2 HIFF Heq). reflexivity. }
split; [|exact Hpres].
intros a Ha Hw. apply (Hfr a Ha). rewrite Hsp. lia.
Qed.

Lemma ix_E_img : forall regs_e regs n i p iv, img_env VAL A_LIM (ix_E regs_e regs n i p iv).
Proof. intros. apply Eimg_env. Qed.

(* the bytes a run left as they were: this walk's runs write nothing outside the frame *)
Ltac ix_nokept HFr UNn :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr
    ltac:(let bb := fresh in let wl := fresh in let wh := fresh in let aa := fresh in
          let Hin := fresh in let Hrr := fresh in let H0 := fresh in
          intros bb wl wh aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [H0 | Hin];
                  [ inversion H0; subst; cbn [base_val] in Hrr; exfalso; lia | ]);
          exact Hin)) as UNn.

(* ---- the loop at +0x70: one turn per index, by induction on the entries still to read ---- *)
Lemma ix_loop : forall AF, AF = AF_fuzz_if_nametoindex \/ AF = AF_index_of ->
 forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
        (bs : list byte) (tab : list (list byte * Z)) (nm : list byte),
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - FUZZ_IF_NAMETOINDEX_AK -> spZ regs <= sp0 ->
  anlk_at SEGS (rdW W memc) LA_G_NL bs ->
  aiftab_at SEGS (rdW W memc) LA_G_NL bs tab ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (LA_G_NL + NK_IF_NAME) (8 * Z.of_nat (length tab)) ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (LA_G_NL + NK_IF_INDEX) (4 * Z.of_nat (length tab)) ->
  acstr_at SEGS (rdW W memc) (aarg regs 0) nm ->
  astrcmp_arg_ni SEGS regs FUZZ_IF_NAMETOINDEX_AK (rdW W memc) (aarg regs 0) nm ->
  (forall j n2 iv q, nth_error tab j = Some (n2, iv) ->
     au64_at SEGS (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat j) q -> 0 <= q < 2 ^ 64 ->
     astrcmp_arg_ni SEGS regs FUZZ_IF_NAMETOINDEX_AK (rdW W memc) q n2) ->
  forall (ni : nat) (i : Z) (mem1 : word -> option byte) (md1 : Model) (regs1 : bvmap 5 word),
  (Z.to_nat (Z.of_nat (length tab) - i) = ni)%nat -> 0 <= i -> i < Z.of_nat (length tab) ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
     aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem1 a) ->
  m_fds md1 = m_fds mdc -> m_fs md1 = m_fs mdc ->
  ix_inv regs regs1 (Z.of_nat (length tab)) i -> ix_saved W mem1 regs ->
  index_of tab nm = index_of (skipn (Z.to_nat i) tab) nm ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AF + 0x70))) mem1 (seg_rom SEGS)) md1)
    (apost SK SEGS B FUZZ_IF_NAMETOINDEX_AK 0
       (fun a => inFP (fuzz_if_nametoindex_awr regs (rdW W memc)) a)
       G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
       (fun ly2 S2 W2 regs2 mem2 md2 =>
          S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
          fuzz_if_nametoindex_apost SEGS regs (rdW W memc) regs2 (rdW W2 mem2))).
Proof.
intros AF HAF G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs tab nm
  HGX HJ0 Hret Hra4 Hgp Htp H16 Hwlo Hwhi HNK HTAB RAN RAI HCS HARG HTARG.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ0 as (HSTK0 & HXO0 & (memS0 & HJi0 & _) & _).
pose proof HJi0 as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HK : FUZZ_IF_NAMETOINDEX_AK = 8272) by reflexivity.
assert (HCEIL : alloc_ceiling <= spZ regs - FUZZ_IF_NAMETOINDEX_AK) by lia.
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof HTAB as (HTn & HT80 & HTe).
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_run_to_x SK B LAWS G HGX XO OUT) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (paj_ret_at (PL := PL_link) (PI := PI)) as RET.
destruct HAF as [-> | ->];
(intros ni; induction ni as [|ni IH];
 intros i mem1 md1 regs1 Hni Hi0 Hilt HJ1 UN1 GR1 Hfd1 Hfs1 HINV HSV HIDX;
 [ exfalso; lia | ];
 destruct (ix_turn_prep W regs memc mem1 mem1 bs tab nm i HTAB RAN RAI HCS HARG HTARG
             ltac:(lia) HCEIL UN1 UN1)
   as (q & iv & n2 & He & Hq & Hiv & Vq1 & Viv1 & RAq1 & RAi1 & CSq1 & CSnm1 & AQ1 & AN1);
 lazymatch goal with
 | |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + (?af + 112))) _ _) _) _ =>
   destruct (ix_seat af G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs regs1
               (Z.of_nat (length tab)) i q iv HJ1 H16 Hwlo Hwhi HINV HSV
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hiv Vq1 Viv1 RAq1 RAi1) as (HS & SHOK);
   pose proof (@eq_refl Z af) as HAFv
 end;
 pose proof (ix_E_img regs regs1 (Z.of_nat (length tab)) i q iv) as HEI;
 assert (XX32 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 32 = Z_to_bv 64 SB)
   by exact (ix_E_ext _ _ _ _ _ _ 0%nat ltac:(lia));
 assert (XX33 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 33
                = Z_to_bv 64 (Z.of_nat (length tab) - i))
   by exact (ix_E_ext _ _ _ _ _ _ 1%nat ltac:(lia));
 assert (XX34 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 34
                = Z_to_bv 64 (IX_NM_LO + 8 * i))
   by exact (ix_E_ext _ _ _ _ _ _ 2%nat ltac:(lia));
 assert (XX35 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 35
                = Z_to_bv 64 (IX_IX_LO + 4 * i))
   by exact (ix_E_ext _ _ _ _ _ _ 3%nat ltac:(lia));
 assert (XX36 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 36 = Z_to_bv 64 q)
   by exact (ix_E_ext _ _ _ _ _ _ 4%nat ltac:(lia));
 assert (XX37 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 37 = Z_to_bv 64 iv)
   by exact (ix_E_ext _ _ _ _ _ _ 5%nat ltac:(lia));
 assert (EE1 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 1 = getr regs 1)
   by (apply (ix_E_reg _ _ _ _ _ _ 1%nat 1%bv); [reflexivity | lia]);
 assert (EE2 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 2 = getr regs 2)
   by (apply (ix_E_reg _ _ _ _ _ _ 2%nat 2%bv); [reflexivity | lia]);
 assert (EE3 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 3 = getr regs 3)
   by (apply (ix_E_reg _ _ _ _ _ _ 3%nat 3%bv); [reflexivity | lia]);
 assert (EE4 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 4 = getr regs 4)
   by (apply (ix_E_reg _ _ _ _ _ _ 4%nat 4%bv); [reflexivity | lia]);
 assert (EE10 : ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 10 = getr regs 10)
   by (apply (ix_E_reg _ _ _ _ _ _ 10%nat 10%bv); [reflexivity | lia]);
 paj_run_tok RUN HS HJ1 SHOK Bspan; [ ix_awr | ];
 ix_nokept HFr UNc;
 pose proof (ix_grow (w_H W) _ _ HG) as GRc; clear HF HFr HG;
 pmkst HS;
 prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3;
 prreg HS (4%bv : bv 5) Q4; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
 assert (UNm : forall a, 0 <= a < 2 ^ 64 ->
            ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
            aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem1 a)
   by (intros a Ha _; exact (UNc a Ha ltac:(intros [])));
 pose proof AQ1 as (_ & _ & AQmem & _ & _ & AQpart);
 pose proof AN1 as (_ & _ & ANmem & _ & _ & ANpart);
 pose proof (ix_cstr_frame_sep W regs mem1 (ms_mem ms) q n2 CSq1 AQpart AQmem UNm) as CSq;
 pose proof (ix_cstr_frame_sep W regs mem1 (ms_mem ms) (aarg regs 0) nm CSnm1 ANpart ANmem UNm) as CSnm;
 pose proof (ix_arg_frame W regs mem1 (ms_mem ms) q n2 AQ1 HCEIL UNm) as AQ;
 pose proof (ix_arg_frame W regs mem1 (ms_mem ms) (aarg regs 0) nm AN1 HCEIL UNm) as AN;
 assert (Hspc : spZ (ms_regs ms) = spZ regs - 80);
 [ unfold spZ in Hsp46 |- *; rewrite Q2, EE2;
   rewrite unsigned_lit_small by lia; lia | ];
 assert (Hgpc : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, EE3; exact Hgp);
 assert (Htpc : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, EE4; exact Htp);
 assert (Hq10 : getr (ms_regs ms) 10 = w64 q) by (rewrite Q10, XX36; reflexivity);
 assert (Hq11 : getr (ms_regs ms) 11 = w64 (aarg regs 0));
 [ rewrite Q11, EE10; unfold aarg, w64; symmetry; apply Z_to_bv_bv_unsigned | ];
 lazymatch type of Q1 with getr _ _ = Z_to_bv 64 (_ + ?kk) =>
   assert (Hrok : YK0s.ret_ok (Z_to_bv 64 (BASE + kk)))
     by (apply ret_ok_codeptr_v; [lia | lia]) end;
 eapply SRr_bind;
 [ exact (ix_call W G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k regs (ms_regs ms) (ms_mem ms)
            q nm n2 _ HGX HJ1 Hspc H16 Hwlo Hwhi Hgpc Htpc Q1 Hrok Hq10 Hq11 CSq CSnm AQ AN) | ];
 cbv beta;
 intros W2 cf Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & Hsame2 & HPres2 & HANS & HFR2 & HGR2);
 jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W) mem2) HPres2 [0; 2]%nat HS2;
 lazymatch type of HS2 with ?Q -> _ => assert (HKEEP : Q) end;
 [ apply Forall_cons;
   [ eapply (region_kept_aview (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) (w_H W)
               (ms_mem ms) mem2 2%nat (spZ regs) (-80) 0 0 0 _);
     [ rewrite EE2; reflexivity
     | intros a Ha; apply HFR2; [lia | lia]
     | exact HGR2 ]
   | apply Forall_cons; [|apply Forall_nil];
     eapply (region_kept_aview (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) (w_H W)
               (ms_mem ms) mem2 35%nat (IX_IX_LO + 4 * i) 0 4 0 0 _);
     [ rewrite XX35; apply unsigned_lit_small; unfold IX_IX_LO, LA_G_NL, NK_IF_INDEX; lia
     | intros a Ha; apply HFR2;
       [ unfold IX_IX_LO, LA_G_NL, NK_IF_INDEX in *; lia
       | unfold IX_IX_LO, LA_G_NL, NK_IF_INDEX in *; lia ]
     | exact HGR2 ] ]
 | specialize (HS2 HKEEP); clear HKEEP ];
 assert (HEI2 : img_env VAL A_LIM
          (havoc (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 64 (map (getr regs2) CLOB)))
   by (apply img_env_havoc; [exact HEI | cbv; lia]);
 assert (UN2m : forall a, 0 <= a < alloc_ceiling ->
           aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a);
 [ intros a Ha; rewrite (HFR2 a ltac:(lia) ltac:(lia)); exact (UNm a ltac:(lia) ltac:(lia)) | ];
 assert (RAq2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF (IX_NM_LO + 8 * i) 8);
 [ apply (ra_shadow_eq (aview SEGS (w_H W) mem1));
   [ exact RAq1
   | intros x Hx; apply UN2m; apply ix_shadow_low;
     unfold IX_NM_LO, LA_G_NL, NK_IF_NAME, kHighMemEnd in *; lia ] | ];
 assert (RAi2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF (IX_IX_LO + 4 * i) 4);
 [ apply (ra_shadow_eq (aview SEGS (w_H W) mem1));
   [ exact RAi1
   | intros x Hx; apply UN2m; apply ix_shadow_low;
     unfold IX_IX_LO, LA_G_NL, NK_IF_INDEX, kHighMemEnd in *; lia ] | ];
 assert (SHOK2 : sh_ok SEGS (SOff 32 0) ix_SH
          (havoc (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) 64 (map (getr regs2) CLOB))
          (mrestrict (w_H W) mem2));
 [ apply (ix_shok _ W mem2 (IX_NM_LO + 8 * i) (IX_IX_LO + 4 * i));
   [ rewrite ew_havoc_old by lia; exact XX32
   | rewrite ew_havoc_old by lia; exact XX34
   | rewrite ew_havoc_old by lia; exact XX35
   | lia | lia | lia | lia | exact RAq2 | exact RAi2 ] | ];
 rewrite <- restrict_mkst_fx in HS2;
 lazymatch type of HS2 with st_ok_pi _ _ ?EV _ _ => set (E2 := EV) in * end;
 assert (HAE2 : env_agree 32 (Ereg regs (ix_extra regs1 (Z.of_nat (length tab)) i q iv)) E2);
 [ unfold E2; split;
   [ intros nn Hnn; rewrite ew_havoc_old by lia; unfold ix_E; apply Eimg_low; unfold A_TEXT; lia
   | reflexivity ] | ];
 psrr_branch_tok RUN BR HS2 SHOK2 Bspan;
 [ (* HIT: the entry's name is the one asked for *)
   prreg HS2 (10%bv : bv 5) R10;
   assert (Hhit : getr regs2 10 = w64 0);
   [ rewrite branch_eq_U in Hc; apply Z.eqb_eq in Hc;
     rewrite U_SOff, Z.add_0_r, YP0m.zcanon_small, (U_lit E2 0) in Hc
       by (pose proof (bv_unsigned_in_range 64 (ew E2 68)) as HR;
           change (bv_modulus 64) with (2 ^ 64) in HR; lia);
     rewrite R10; apply bv_eq; rewrite Hc; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | ];
   assert (Hn2 : n2 = nm) by (apply HANS; exact Hhit);
   paj_run_tok RUN HS2 HJ2 SHOK2 Bspan; [ ix_awr | ];
   ix_nokept HFr UN4; pose proof (ix_grow (w_H W) _ _ HG) as GR4; clear HF HFr HG;
   prreg HS2 (1%bv : bv 5) P1; prreg HS2 (10%bv : bv 5) P10;
   lazymatch type of HS2 with st_ok_pi _ _ ?EV _ (restrict _ ?msF) =>
     rename msF into msH; set (E3 := EV) in * end;
   assert (HAE3 : env_agree 32 (Ereg regs (ix_extra regs1 (Z.of_nat (length tab)) i q iv)) E3);
   [ unfold E3; split;
     [ intros nn Hnn; rewrite !ew_ewset_other by lia; unfold E2; rewrite ew_havoc_old by lia;
       unfold ix_E; apply Eimg_low; unfold A_TEXT; lia
     | reflexivity ] | ];
   assert (UNF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
             aview SEGS (w_H W) (ms_mem msH) a = aview SEGS (w_H W) memc a);
   [ intros a Ha Hw; rewrite (UN4 a Ha ltac:(intros [])), (HFR2 a Ha ltac:(lia)), (UNm a Ha Hw);
     exact (UN1 a Ha Hw) | ];
   assert (GRF : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msH) a)
     by (intros a Ha; apply GR4, HGR2, GRc, GR1, Ha);
   assert (HR10 : getr (ms_regs msH) 10 = w64 (index_of tab nm));
   [ rewrite P10; unfold E2; rewrite ew_havoc_old by lia; rewrite XX37;
     rewrite HIDX, (ix_of_hit tab (Z.to_nat i) n2 iv nm He Hn2); reflexivity | ];
   pose proof (aregs_preserved_of_st_ok SEGS _ E3 _ _ regs (ix_extra regs1 (Z.of_nat (length tab)) i q iv)
                 HS2 HAE3 ltac:(vm_compute; reflexivity)) as HPF;
   pose proof Hret as Hret'; unfold YK0s.ret_ok in Hret';
   eapply (RET W _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity));
   intros mat';
   rewrite P1; unfold E2; rewrite ew_havoc_old by lia; rewrite EE1, Hret';
   apply (ix_exit G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msH) (ms_mem msH) _
            bs tab nm HJ0);
   [ apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ2
   | exact Hwlo | exact Hwhi
   | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); rewrite Hsame2;
     repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfd1
   | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); rewrite Hsame2;
     repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfs1
   | exact HPF | exact UNF | exact GRF | exact HNK | exact HTAB | exact HCS | exact HR10 ]
 | (* MISS: the entry's name is another one *)
   prreg HS2 (10%bv : bv 5) R10;
   assert (Hn2 : n2 <> nm);
   [ intros Heq; apply (proj2 HANS) in Heq; rewrite R10 in Heq;
     rewrite branch_eq_U in Hc; apply Z.eqb_neq in Hc; apply Hc;
     rewrite U_SOff, Z.add_0_r, YP0m.zcanon_small, (U_lit E2 0)
       by (pose proof (bv_unsigned_in_range 64 (ew E2 68)) as HR;
           change (bv_modulus 64) with (2 ^ 64) in HR; lia);
     rewrite Heq; unfold w64; apply unsigned_lit_small; lia | ];
   paj_run_tok RUN HS2 HJ2 SHOK2 Bspan; [ ix_awr | ];
   ix_nokept HFr UN5; pose proof (ix_grow (w_H W) _ _ HG) as GR5; clear HF HFr HG;
   assert (U33 : U E2 (SOff 33 (-1)) = Z.of_nat (length tab) - i - 1);
   [ rewrite U_SOff; unfold E2; rewrite ew_havoc_old by lia; rewrite XX33, unsigned_lit_small by lia;
     apply YP0m.zcanon_small; lia | ];
   assert (HIXm : index_of tab nm = index_of (skipn (Datatypes.S (Z.to_nat i)) tab) nm)
     by (rewrite HIDX; exact (ix_of_miss tab (Z.to_nat i) n2 iv nm He Hn2));
   psrr_branch_tok RUN BR HS2 SHOK2 Bspan;
   [ (* BACK: one more entry to read *)
     rewrite branch_ne_U, U33, (U_lit E2 0) in Hc0 by lia;
     apply negb_true_iff, Z.eqb_neq in Hc0;
     lazymatch type of HAFv with ?afv = _ =>
       paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspan (afv + 0x70) end;
     [ ix_awr | ];
     ix_nokept HFr UN6; pose proof (ix_grow (w_H W) _ _ HG) as GR6; clear HF HFr HG;
     lazymatch type of HS2 with st_ok_pi _ _ _ ?ssF (restrict _ ?msF) =>
       rename msF into msB; set (ssB := ssF) in HS2 end;
     assert (EW2 : forall a, (a < 64)%nat ->
               ew E2 a = ew (ix_E regs regs1 (Z.of_nat (length tab)) i q iv) a)
       by (intros a Ha; unfold E2; apply ew_havoc_old; lia);
     assert (Y32 : ew E2 32 = Z_to_bv 64 SB) by (rewrite EW2 by lia; exact XX32);
     assert (Y33 : ew E2 33 = Z_to_bv 64 (Z.of_nat (length tab) - i)) by (rewrite EW2 by lia; exact XX33);
     assert (Y34 : ew E2 34 = Z_to_bv 64 (IX_NM_LO + 8 * i)) by (rewrite EW2 by lia; exact XX34);
     assert (Y35 : ew E2 35 = Z_to_bv 64 (IX_IX_LO + 4 * i)) by (rewrite EW2 by lia; exact XX35);
     assert (HNMb : IX_NM_LO = 6417776) by reflexivity;
     assert (HIXb : IX_IX_LO = 6418416) by reflexivity;
     assert (HSBb : SB = 2147450880) by reflexivity;
     assert (BREG : forall r : bv 5, getr (ms_regs msB) r = sv_denot E2 (sr_get (ss_regs ssB) r))
       by (intros r; exact (st_ok_pi_restrict_reg (w_H W) E2 ssB msB r HS2));
     assert (HINVB : ix_inv regs (ms_regs msB) (Z.of_nat (length tab)) (i + 1));
     [ unfold ix_inv; rewrite !BREG; unfold ssB;
       repeat split;
       lazymatch goal with |- sv_denot _ (sr_get ?L ?R) = _ =>
         let v := eval vm_compute in (sr_get L R) in change (sr_get L R) with v end;
       first
       [ rewrite (ix_soffc E2 2 (-80) (spZ regs)); [reflexivity | rewrite EW2 by lia; rewrite EE2;
           symmetry; apply Z_to_bv_bv_unsigned | lia | lia]
       | rewrite ix_soff0, EW2 by lia; first [exact EE3 | exact EE4 | exact EE10
           | apply (ix_E_reg _ _ _ _ _ _ 24%nat 24%bv); [reflexivity | lia]
           | apply (ix_E_reg _ _ _ _ _ _ 25%nat 25%bv); [reflexivity | lia]
           | apply (ix_E_reg _ _ _ _ _ _ 26%nat 26%bv); [reflexivity | lia]
           | apply (ix_E_reg _ _ _ _ _ _ 27%nat 27%bv); [reflexivity | lia]
           | exact XX32 ]
       | rewrite (ix_soffc E2 35 4 (IX_IX_LO + 4 * i) Y35) by lia; f_equal; lia
       | rewrite (ix_soffc E2 34 8 (IX_NM_LO + 8 * i) Y34) by lia; f_equal; lia
       | rewrite (ix_soffc E2 33 (-1) (Z.of_nat (length tab) - i) Y33) by lia; f_equal; lia
       | rewrite (ix_denot_shx1 E2 34 (IX_NM_LO + 8 * i) SB Y34 Y32) by lia; f_equal;
         replace (IX_NM_LO + 8 * (i + 1)) with ((IX_NM_LO + 8 * i) + 1 * 8) by lia;
         rewrite Z_div_plus_full by lia; lia ] | ];
     assert (UNfr : forall a, spZ regs - 80 <= a < spZ regs ->
               aview SEGS (w_H W) (ms_mem msB) a = aview SEGS (w_H W) mem1 a);
     [ intros a Ha; rewrite (UN6 a ltac:(lia) ltac:(intros [])), (UN5 a ltac:(lia) ltac:(intros [])),
         (HFR2 a ltac:(lia) ltac:(lia)); exact (UNc a ltac:(lia) ltac:(intros [])) | ];
     assert (HSVB : ix_saved W (ms_mem msB) regs);
     [ unfold ix_saved in HSV |- *;
       destruct HSV as (S7 & S6 & S5 & S4 & S3 & S2 & S1 & S0 & SRA);
       repeat split;
       (eapply ix_val_frame; [eassumption | intros x Hx; apply (mbyte_of_aview SEGS); apply UNfr; lia]) | ];
     assert (UNB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
               aview SEGS (w_H W) (ms_mem msB) a = aview SEGS (w_H W) memc a);
     [ intros a Ha Hw; rewrite (UN6 a Ha ltac:(intros [])), (UN5 a Ha ltac:(intros [])),
         (HFR2 a Ha ltac:(lia)), (UNm a Ha Hw); exact (UN1 a Ha Hw) | ];
     assert (GRB : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msB) a)
       by (intros a Ha; apply GR6, GR5, HGR2, GRc, GR1, Ha);
     assert (HIDXB : index_of tab nm = index_of (skipn (Z.to_nat (i + 1)) tab) nm);
     [ rewrite Z2Nat.inj_add by lia; change (Z.to_nat 1) with 1%nat; rewrite Nat.add_1_r; exact HIXm | ];
     pmkst HS2;
     lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcl)) _ _) _) _ =>
       lazymatch type of HAFv with ?afv = _ =>
         replace pcl with (afv + 0x70) by (vm_compute; reflexivity) end end;
     apply (IH (i + 1) (ms_mem msB) _ (ms_regs msB));
     [ lia | lia | lia | exact HJ2 | exact UNB | exact GRB
     | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); rewrite Hsame2;
       repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfd1
     | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); rewrite Hsame2;
       repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfs1
     | exact HINVB | exact HSVB | exact HIDXB ]
   | (* END: the last entry missed too; the answer is 0 *)
     rewrite branch_ne_U, U33, (U_lit E2 0) in Hc0 by lia;
     apply negb_false_iff, Z.eqb_eq in Hc0;
     paj_run_tok RUN HS2 HJ2 SHOK2 Bspan; [ ix_awr | ];
     ix_nokept HFr UN6; pose proof (ix_grow (w_H W) _ _ HG) as GR6; clear HF HFr HG;
     prreg HS2 (1%bv : bv 5) P1; prreg HS2 (10%bv : bv 5) P10;
     lazymatch type of HS2 with st_ok_pi _ _ ?EV _ (restrict _ ?msF) =>
       rename msF into msH; set (E3 := EV) in * end;
     assert (HAE3 : env_agree 32 (Ereg regs (ix_extra regs1 (Z.of_nat (length tab)) i q iv)) E3);
     [ unfold E3; split;
       [ intros nn Hnn; rewrite ?ew_ewset_other by lia; unfold E2; rewrite ew_havoc_old by lia;
         unfold ix_E; apply Eimg_low; unfold A_TEXT; lia
       | reflexivity ] | ];
     assert (UNF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
               aview SEGS (w_H W) (ms_mem msH) a = aview SEGS (w_H W) memc a);
     [ intros a Ha Hw; rewrite (UN6 a Ha ltac:(intros [])), (UN5 a Ha ltac:(intros [])),
         (HFR2 a Ha ltac:(lia)), (UNm a Ha Hw); exact (UN1 a Ha Hw) | ];
     assert (GRF : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msH) a)
       by (intros a Ha; apply GR6, GR5, HGR2, GRc, GR1, Ha);
     assert (HIXV : index_of tab nm = 0) by (rewrite HIXm; apply ix_of_end; lia);
     assert (HR10 : getr (ms_regs msH) 10 = w64 (index_of tab nm)) by (rewrite P10, HIXV; reflexivity);
     pose proof (aregs_preserved_of_st_ok SEGS _ E3 _ _ regs (ix_extra regs1 (Z.of_nat (length tab)) i q iv)
                   HS2 HAE3 ltac:(vm_compute; reflexivity)) as HPF;
     pose proof Hret as Hret'; unfold YK0s.ret_ok in Hret';
     eapply (RET W _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity));
     intros mat';
     rewrite P1; unfold E3, E2; rewrite ew_havoc_old by lia; rewrite EE1, Hret';
     apply (ix_exit G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msH) (ms_mem msH) _
              bs tab nm HJ0);
     [ apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ2
     | exact Hwlo | exact Hwhi
     | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); rewrite Hsame2;
       repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfd1
     | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); rewrite Hsame2;
       repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfs1
     | exact HPF | exact UNF | exact GRF | exact HNK | exact HTAB | exact HCS | exact HR10 ] ] ]).
Qed.



(* the bytes the entry run left as they were: all but its own 80-byte frame *)
Ltac ix_kept_fr HFr sp UNn :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a : Z => sp - 80 <= a < sp) HFr
    ltac:(let bb := fresh in let wl := fresh in let wh := fresh in let aa := fresh in
          let Hin := fresh in let Hrr := fresh in let H0 := fresh in
          intros bb wl wh aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [H0 | Hin];
                  [ inversion H0; subst; cbn [base_val] in Hrr;
                    repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- _ =>
                      lazymatch type of Hrr with context [ew _ n] => rewrite U in Hrr end end;
                    cbv beta; lia | ]);
          destruct Hin)) as UNn.

(* THE CORE: the walk from either entry *)
Theorem if_lookup_aproof : forall AF, AF = AF_fuzz_if_nametoindex \/ AF = AF_index_of ->
  forall rlo rhi, aleaf_rd SK SEGS rlo rhi B (pa_val A_TEXT + AF) FUZZ_IF_NAMETOINDEX_AK 0 []
    (fuzz_if_nametoindex_apre SEGS) (fuzz_if_nametoindex_ard SEGS) fuzz_if_nametoindex_awr
    (fuzz_if_nametoindex_apost SEGS).
Proof.
intros AF HAF rlo rhi. unfold aleaf_rd.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HRD HP.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
destruct HP as (bs & tab & nm & HNK & HTAB & RAN & RAI & Hnm0 & HCS & HARG & HTARG).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as HJ0.
pose proof HJ as (HSTK0 & HXO0 & (memS0 & HJi0 & _) & _).
pose proof HJi0 as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HK : FUZZ_IF_NAMETOINDEX_AK = 8272) by reflexivity.
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof HTAB as (HTn & HT80 & HTe).
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_run_to_x SK B LAWS G HGX XO OUT) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (paj_ret_at (PL := PL_link) (PI := PI)) as RET.
unfold cfg_at, w64.
destruct HAF as [-> | ->];
( lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?af)) _ _) _) _ =>
    pose proof (@eq_refl Z af) as HAFv end;
  destruct (Nat.eq_dec (length tab) 0) as [Hz | Hnz];
  [ (* the empty table: `blez` to +0xa4, the answer 0 *)
    lazymatch type of HAFv with ?afv = _ =>
    pose proof (ix_entry afv 0 0 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs
                  HJ H16 Hwlo Hwhi HNK ltac:(lia) ltac:(lia) ltac:(lia)) as HS end
  | lazymatch type of HAFv with ?afv = _ =>
    pose proof (ix_entry afv 1 80 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs
                  HJ H16 Hwlo Hwhi HNK ltac:(lia) ltac:(lia) ltac:(lia)) as HS end ];
  set (E0 := Eimg (Ereg regs (ix_e_extra (nk_n_if bs)))) in HS;
  assert (HEI : img_env VAL A_LIM E0) by (apply Eimg_env);
  assert (EE1 : ew E0 1 = getr regs 1)
    by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1%nat 1%bv eq_refl));
  assert (EE2 : ew E0 2 = getr regs 2)
    by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2%nat 2%bv eq_refl));
  assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite EE2; reflexivity);
  assert (HAE0 : env_agree 32 (Ereg regs (ix_e_extra (nk_n_if bs))) E0)
    by (unfold E0; split; [ intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity ]);
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E0 (rdW W memc)) by (unfold sh_ok; apply Forall_nil);
  [ (* EMPTY *)
    paj_run_tok RUN HS HJ SHOK Bspan; [ ix_awr | ];
    ix_kept_fr HFr (spZ regs) UNk; pose proof (ix_grow (w_H W) _ _ HG) as GRk; clear HF HFr HG;
    prreg HS (1%bv : bv 5) P1; prreg HS (10%bv : bv 5) P10;
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) => rename msF into msH end;
    assert (UNF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
              aview SEGS (w_H W) (ms_mem msH) a = aview SEGS (w_H W) memc a)
      by (intros a Ha Hw; apply UNk; [exact Ha | cbv beta; lia]);
    assert (Htab0 : tab = []) by (destruct tab; [reflexivity | discriminate]);
    assert (HR10 : getr (ms_regs msH) 10 = w64 (index_of tab nm)) by (rewrite Htab0, P10; reflexivity);
    pose proof (aregs_preserved_of_st_ok SEGS _ E0 _ _ regs (ix_e_extra (nk_n_if bs)) HS HAE0
                  ltac:(vm_compute; reflexivity)) as HPF;
    pose proof Hret as Hret'; unfold YK0s.ret_ok in Hret';
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    rewrite P1, EE1, Hret';
    apply (ix_exit G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msH) (ms_mem msH) _
             bs tab nm HJ0);
    [ apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ
    | exact Hwlo | exact Hwhi
    | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
    | exact HPF | exact UNF | exact GRk | exact HNK | exact HTAB | exact HCS | exact HR10 ]
  | (* NON-EMPTY *)
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?af)) _ _) _) _ =>
      paj_run_to_tok RUNTO HS HJ SHOK Bspan (af + 0x70) end;
    [ ix_awr | ];
    ix_kept_fr HFr (spZ regs) UNk; pose proof (ix_grow (w_H W) _ _ HG) as GRk; clear HF HFr HG;
    lazymatch type of HS with st_ok_pi _ _ _ ?ssF (restrict _ ?msF) =>
      rename msF into msL; set (ssL := ssF) in HS end;
    assert (ER : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> (m < 32)%nat -> ew E0 m = getr regs r)
      by (intros m r Hm Hl; unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ m r Hm));
    assert (X32 : ew E0 32 = Z_to_bv 64 SB)
      by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0%nat));
    assert (X33 : ew E0 33 = Z_to_bv 64 (nk_n_if bs))
      by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1%nat));
    assert (Eg : ew E0 (A_OBJ 2) = Z_to_bv 64 LA_G_NL);
    [ unfold E0; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
      destruct ix_vals as (_ & V2 & _); rewrite V2; reflexivity | ];
    change (A_OBJ 2) with 243%nat in Eg;
    assert (HNMb : IX_NM_LO = 6417776) by reflexivity;
    assert (HIXb : IX_IX_LO = 6418416) by reflexivity;
    assert (HSBb : SB = 2147450880) by reflexivity;
    assert (HGb : LA_G_NL = 6146752) by reflexivity;
    assert (BREG : forall r : bv 5, getr (ms_regs msL) r = sv_denot E0 (sr_get (ss_regs ssL) r))
      by (intros r; exact (st_ok_pi_restrict_reg (w_H W) E0 ssL msL r HS));
    assert (HINV0 : ix_inv regs (ms_regs msL) (Z.of_nat (length tab)) 0);
    [ unfold ix_inv; rewrite !BREG; unfold ssL;
      repeat split;
      lazymatch goal with |- sv_denot _ (sr_get ?L ?R) = _ =>
        let v := eval vm_compute in (sr_get L R) in change (sr_get L R) with v end;
      first
      [ rewrite (ix_soffc E0 2 (-80) (spZ regs)); [reflexivity | rewrite EE2;
          symmetry; apply Z_to_bv_bv_unsigned | lia | lia]
      | rewrite ix_soff0, X32; reflexivity
      | rewrite ix_soff0, X33; f_equal; lia
      | rewrite ix_soff0; apply ER; [reflexivity | lia]
      | rewrite (ix_soffc E0 243 271664 LA_G_NL Eg) by lia; f_equal; unfold IX_IX_LO, NK_IF_INDEX; lia
      | rewrite (ix_soffc E0 243 271024 LA_G_NL Eg) by lia; f_equal; unfold IX_NM_LO, NK_IF_NAME; lia
      | rewrite (ix_denot_shx_e E0 243 32 271024 LA_G_NL SB Eg X32) by lia; f_equal;
        unfold IX_NM_LO, NK_IF_NAME; lia ] | ];
    pose proof (st_ok_region_nth (segs := SEGS) E0 (abs_ss VAL ssL) (restrict (w_H W) msL) 0 _ HS eq_refl) as HR0;
    assert (HSV0 : ix_saved W (ms_mem msL) regs);
    [ unfold ix_saved;
      repeat split;
      lazymatch goal with |- val_mem _ _ (spZ regs - ?o) 8 (bv_unsigned (getr regs ?r)) =>
        let rn := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
        pose proof (field_of_region_any E0 _ 2%nat (spZ regs) _ _ _ _ _ (- o) 8%N (SOff rn 0) HR0 Usp
                      ltac:(repeat (first [left; reflexivity | right])) ltac:(lia)) as HV;
        rewrite ix_soff0 in HV; rewrite (ER rn r eq_refl ltac:(lia)) in HV;
        rewrite Z.mod_small in HV
          by (pose proof (bv_unsigned_in_range 64 (getr regs r)) as HRg;
              change (bv_modulus 64) with (2 ^ 64) in HRg; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia);
        replace (spZ regs - o) with (spZ regs + - o) by lia; exact HV end | ];
    assert (UNF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FUZZ_IF_NAMETOINDEX_AK <= a < spZ regs) ->
              aview SEGS (w_H W) (ms_mem msL) a = aview SEGS (w_H W) memc a)
      by (intros a Ha Hw; apply UNk; [exact Ha | cbv beta; lia]);
    pmkst HS;
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcl)) _ _) _) _ =>
      lazymatch type of HAFv with ?afv = _ =>
        replace pcl with (afv + 0x70) by (vm_compute; reflexivity) end end;
    lazymatch type of HAFv with ?afv = _ =>
    apply (ix_loop afv ltac:(first [left; reflexivity | right; reflexivity])
             G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs tab nm
             HGX HJ0 Hret Hra4 Hgp Htp H16 Hwlo Hwhi HNK HTAB RAN RAI HCS HARG HTARG
             (length tab) 0 (ms_mem msL) _ (ms_regs msL)) end;
    [ lia | lia | lia | exact HJ | exact UNF | exact GRk
    | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
    | exact HINV0 | exact HSV0 | reflexivity ] ] ).
Qed.


(* THE CONTRACT at fuzz_if_nametoindex's entry: the core at AF_fuzz_if_nametoindex *)
Theorem fuzz_if_nametoindex_aproof : forall rlo rhi, fuzz_if_nametoindex_acontract SK SEGS rlo rhi B.
Proof.
  intros rlo rhi. unfold fuzz_if_nametoindex_acontract.
  replace FUZZ_IF_NAMETOINDEX_A with (pa_val A_TEXT + AF_fuzz_if_nametoindex)
    by (destruct ix_vals as (_ & _ & _ & VB); rewrite VB; reflexivity).
  exact (if_lookup_aproof AF_fuzz_if_nametoindex (or_introl eq_refl) rlo rhi).
Qed.

End w.

Print Assumptions if_lookup_aproof.
Print Assumptions fuzz_if_nametoindex_aproof.
