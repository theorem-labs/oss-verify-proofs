(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the journal rule of a call to the stack-frame release entry (aj_stack_free_at of proofs/cgif/cgif_rgb_fuzzer/lib/YC05.v) and the write rule it uses (ajournal_after_write_win of that file), restated over the journal of the cgif_file_fuzzer proof (YCbq.ajournal) as libreac/fuzz_grant holds it; module names. The released shadow span is sf_span cid n (StackFreeDef.v), not n / 8. The rule has no frame_flag_law hypothesis: the facts it needs about the frame's flag byte (owned, an application address, outside the image) come from AR_laws (al_flag, al_client_img). *)
(* Modified by Theorem Labs, 2026-10: copied by path from libreac/fuzz_grant (a working branch 16327857853; the same text as a working branch c3bfa00452c) with only the module prefix changed to libreac.fuzz_disco. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Reusable/StackFreeJournal.v, with its module paths and module names changed; 698 of its 821 lines of code are new or changed and 116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxExit.v, with its module names changed; 3088 of its 3170 lines of code are new or changed and 739 lines of the source are left out. *)
(* The join phase of the ASan walk of fuzz_boxreg's LLVMFuzzerTestOneInput (fuzz_boxreg.asan, image A):
   0x80ab4 (GP_K) .. 0x80cec, the block the C source writes as

       check (r, fabric); check_kept (r, &prev, renamed);

   and the back edge of the operation loop. The phase proves `gb_join` (lib/A/Prog/BoxLxDefs.v's vocabulary):
   from the cut GI_K it reaches the entry function's post-condition, through GI_J (i + 1) when i + 1 <> 64 and
   through GI_X when i + 1 = 64.

   The walk, slot by slot:
   - 0x80ab4 .. 0x80abc: a0 = r (s4), a1 = fabric (s9), `jal check`. The contract lib/A/Prog/Check.v tcheck_spec
     applies with the table's bytes bs' and Pau's boxreg_B16 bs' (GI_K carries boxreg_inv bs'), its fabric
     (bx_fabric bs' = bx_fabric bs) and the image's ZERO (A_OBJ 6) facts; the call writes nothing this phase reads.
   - 0x80ac0 .. 0x80ac8: prev.n is read at F + 0x40 + 280 (no shadow test in the code) and the loop is skipped when
     it is 0; `prev` holds bs, so prev.n = bx_n bs <= 5 (boxreg_B1).
   - 0x80aec .. 0x80bd4: check_kept inlined, one turn per row j < bx_n bs. Each turn reads r->box[j].base / .nch /
     .pinned and prev.box[j]'s three fields, each after the ASan check of its shadow byte: r's byte through the slot
     0x38 cursor (shadow_of_addr (r + 8) + 7 j, the registry block's shadow, 0 by AR's shadow law) and prev's by the
     shifted address ((prev + 56 j + c) >> 3) + s2 (the frame's shadow, 0 inside the turn, GSH_it). The three
     `bne` aborts are refuted by Pau's llvm_kept (lib/Prog/LLVMFuzzerTestOneInput_inv.v): the row keeps its base,
     width and `pinned`. Then bcmp (prev.box[j].mac, ZERO, 6) and, when that MAC is not zero6, bcmp
     (prev.box[j].mac, r->box[j].mac, 6), both through the bcmp wrapper (abcmp_realizes): llvm_kept gives the MACs
     equal in that case, so the abort at 0x80bb0 is not reached. When 56 j <> 56 ren (j <> ren) the turn also calls
     strncmp (prev.box[j].name, r->box[j].name, 32) through the strncmp wrapper (astrncmp_realizes, a Theorem Labs lane's form):
     the two name fields hold the same bytes, so its answer is 0 and the abort at 0x80bc8 is not reached.
   - 0x80c40 .. 0x80cdc: mac and prev go out of scope again - 37 shadow bytes of the frame (offset 4, and 8 .. 43)
     are set to 0xf8, which turns GSH_it back into GSH_J.
   - 0x80cc8 .. 0x80cec: s5 = slot 0x68 + 1 = i + 1 and s9 = slot 0x50 = the fabric; the turn's back edge takes
     0x801ec (GI_J (i + 1)) when i + 1 <> 64 and 0x80e14 (GI_X) otherwise.

   The strncmp wrapper's two read-only premises (lib/A/Rt/StrncmpDef.v, the frozen form): fm_rom_viewN at the call
   comes from gb_base's arodata_okP carried by the journal (lib/A/Rt/StrncmpView.v fm_rom_viewN_of_arodata), and
   fm_rom_viewO is the Section hypothesis HROMO (true in every AR state), as case 0 states it. check's contract takes
   musl memchr's constant words as HMCH. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YImgTop YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC4b YC85 BoxFrame BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit Check BoxLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef StrncmpDef StrncmpView.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg LLVMFuzzerTestOneInput_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the pcs of this phase, as offsets in the listing ---- *)
Definition JP_call : Z := 0xb70.   (* 0x80abc, the slot after `jal check` is 0xb74 *)
Definition JP_ret : Z := 0xb74.    (* 0x80ac0, where check returns                 *)
Definition JP_head : Z := 0xba0.   (* 0x80aec, the head of the check_kept loop     *)
Definition JP_b1 : Z := 0xc50.     (* 0x80b9c, after the first bcmp                *)
Definition JP_b2a : Z := 0xc54.    (* 0x80ba0, the second bcmp's arguments         *)
Definition JP_b2 : Z := 0xc64.     (* 0x80bb0, after the second bcmp               *)
Definition JP_ren : Z := 0xc68.    (* 0x80bb4, `beq s11, s6`                       *)
Definition JP_sc : Z := 0xc7c.     (* 0x80bc8, after strncmp                       *)
Definition JP_next : Z := 0xc80.   (* 0x80bcc, the turn's tail                     *)
Definition JP_sh : Z := 0xcf4.     (* 0x80c40, the re-poisoning block              *)

(* ---- the symbolic states the walk is seated in ---- *)
(* The atoms: 0 .. 31 the registers at the seat (Ereg), 32 .. the seat's own values (the `extra` list). The
   shadow checks of the code compute ((x >> 3) + s2) with s2 the shadow base, register 18; the engine reads such a
   byte through an alias (shadow_norm, YP0i.v) when x's base atom has one. *)
Definition JBx : sv := SOff 18%nat 0.
(* No token load happens in this phase (every shadow byte it reads is a chunk of a region), so the span the
   token machinery protects is empty; the only write window, the frame's shadow [4, 44), is then `cells_safe_b`. *)
Definition JBspan : Z * Z := (0, 0).

Fixpoint jn_sh_chunks_from (q : Z) (sh : list Z) : list YP09.chunk :=
  match sh with
  | [] => []
  | v :: t => YP09.mkChunk q (CVal 1 (SLit v)) :: jn_sh_chunks_from (q + 1) t
  end.
(* The frame's shadow bytes as chunks, one per byte. *)
Definition jn_sh_chunks (sh : list Z) : list YP09.chunk := jn_sh_chunks_from 0 sh.

(* 0x80c40, the re-poisoning block: the spill slots 0x50 (the fabric, atom 32) and 0x68 (i, atom 33) at s1, and
   the frame's 52 shadow bytes at s8, of which [4, 44) may be written. *)
Definition jn_R_slots_tail : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 152 0 0
    [YP09.mkChunk 0x50 (CVal 8 (SOff 32%nat 0)); YP09.mkChunk 0x68 (CVal 8 (SOff 33%nat 0))].
Definition jn_R_sh : YP09.region := YP09.mkRegion (Some 24%nat) 0 64 4 44 (jn_sh_chunks GSH_it).
Definition jn_AF_sh : list (nat * afact) := [(24%nat, mkAF SHADOW_OFF (2 ^ 47) 0)].
Definition jn_ss_tail : sstate :=
  mkSS JP_sh sr_atoms [jn_R_slots_tail; jn_R_sh] None (mkFacts jn_AF_sh [] []).

Lemma jn_sh_chunks_from_In : forall sh j q, (j < length sh)%nat ->
  In (YP09.mkChunk (q + Z.of_nat j) (CVal 1 (SLit (nth j sh 0)))) (jn_sh_chunks_from q sh).
Proof.
intros sh. induction sh as [|v t IH]; intros j q Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; cbn [jn_sh_chunks_from nth].
- left. rewrite Z.add_0_r. reflexivity.
- right. replace (q + Z.of_nat (S j)) with ((q + 1) + Z.of_nat j) by lia. apply IH. lia.
Qed.

(* ---- bytes of the registry, as numbers ---- *)
Definition jn_b (bs : list byte) (q : Z) : Z := bv_unsigned (nth (Z.to_nat q) bs (Z_to_bv 8 0)).
Definition jn_u (bs : list byte) (q : Z) : Z :=
  jn_b bs q + 256 * (jn_b bs (q + 1) + 256 * (jn_b bs (q + 2) + 256 * jn_b bs (q + 3))).

Lemma jn_b_range : forall bs q, 0 <= jn_b bs q < 256.
Proof.
intros bs q. unfold jn_b. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat q) bs (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma jn_u_range : forall bs q, 0 <= jn_u bs q < 2 ^ 32.
Proof.
intros bs q. unfold jn_u.
pose proof (jn_b_range bs q). pose proof (jn_b_range bs (q + 1)).
pose proof (jn_b_range bs (q + 2)). pose proof (jn_b_range bs (q + 3)). lia.
Qed.

Lemma jn_skipn_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
intros A l. induction l as [|x l IH]; intros k d Hk; cbn [length] in Hk; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma jn_bsub4 : forall (bs : list byte) q, 0 <= q -> q + 4 <= Z.of_nat (length bs) ->
  Boxreg.bsub bs q 4 = [nth (Z.to_nat q) bs (Z_to_bv 8 0); nth (Z.to_nat (q + 1)) bs (Z_to_bv 8 0);
                        nth (Z.to_nat (q + 2)) bs (Z_to_bv 8 0); nth (Z.to_nat (q + 3)) bs (Z_to_bv 8 0)].
Proof.
intros bs q H0 H1. unfold Boxreg.bsub. change (Z.to_nat 4) with 4%nat.
rewrite (jn_skipn_cons bs (Z.to_nat q) (Z_to_bv 8 0)) by lia.
rewrite (jn_skipn_cons bs (S (Z.to_nat q)) (Z_to_bv 8 0)) by lia.
rewrite (jn_skipn_cons bs (S (S (Z.to_nat q))) (Z_to_bv 8 0)) by lia.
rewrite (jn_skipn_cons bs (S (S (S (Z.to_nat q)))) (Z_to_bv 8 0)) by lia.
cbn [firstn].
replace (S (Z.to_nat q)) with (Z.to_nat (q + 1)) by lia.
replace (S (Z.to_nat (q + 1))) with (Z.to_nat (q + 2)) by lia.
replace (S (Z.to_nat (q + 2))) with (Z.to_nat (q + 3)) by lia.
reflexivity.
Qed.

Lemma jn_rd4 : forall bs q, 0 <= q -> q + 4 <= Z.of_nat (length bs) ->
  Boxreg.rd4 bs q = bv_swrap 32 (jn_u bs q).
Proof.
intros bs q H0 H1. unfold Boxreg.rd4. rewrite (jn_bsub4 bs q H0 H1).
rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val.
cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val].
unfold jn_u, jn_b. f_equal. lia.
Qed.

Lemma jn_u_of_rd4 : forall bs q, 0 <= q -> q + 4 <= Z.of_nat (length bs) ->
  0 <= Boxreg.rd4 bs q -> jn_u bs q = Boxreg.rd4 bs q.
Proof.
intros bs q H0 H1 Hpos. pose proof (jn_u_range bs q) as Hr.
rewrite (jn_rd4 bs q H0 H1) in *.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
change (2 ^ Z.of_N 32) with (2 ^ 32) in *.
Z.div_mod_to_equations. lia.
Qed.

(* The byte the machine reads: the i-th byte of the 4-byte little-endian word at q. *)
Lemma jn_u_byte : forall bs q k, (k < 4)%nat -> (jn_u bs q / 2 ^ (8 * Z.of_nat k)) mod 256 = jn_b bs (q + Z.of_nat k).
Proof.
intros bs q k Hk. unfold jn_u.
pose proof (jn_b_range bs q) as R0. pose proof (jn_b_range bs (q + 1)) as R1.
pose proof (jn_b_range bs (q + 2)) as R2. pose proof (jn_b_range bs (q + 3)) as R3.
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- change (q + Z.of_nat 0) with (q + 0). rewrite Z.add_0_r.
  change (2 ^ (8 * Z.of_nat 0)) with 1. Z.div_mod_to_equations. lia.
- change (2 ^ (8 * Z.of_nat 1)) with 256. replace (q + Z.of_nat 1) with (q + 1) by lia.
  Z.div_mod_to_equations. lia.
- change (2 ^ (8 * Z.of_nat 2)) with 65536. replace (q + Z.of_nat 2) with (q + 2) by lia.
  Z.div_mod_to_equations. lia.
- change (2 ^ (8 * Z.of_nat 3)) with 16777216. replace (q + Z.of_nat 3) with (q + 3) by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* ---- the C string a 32-byte name field holds ---- *)
Fixpoint jn_pre (l : list byte) : list Z :=
  match l with
  | [] => []
  | b :: t => if bv_unsigned b =? 0 then [] else bv_unsigned b :: jn_pre t
  end.

Lemma jn_pre_nonzero : forall l, Forall (fun c => c <> 0) (jn_pre l).
Proof.
induction l as [|b t IH]; cbn [jn_pre]; [constructor|].
destruct (bv_unsigned b =? 0) eqn:E; [constructor|].
constructor; [apply Z.eqb_neq; exact E | exact IH].
Qed.

Lemma jn_pre_len : forall l, In (Z_to_bv 8 0) l -> (length (jn_pre l) < length l)%nat.
Proof.
induction l as [|b t IH]; intros H; cbn [jn_pre length In] in H |- *; [destruct H|].
destruct (bv_unsigned b =? 0) eqn:E; cbn [length].
- lia.
- destruct H as [H|H].
  + exfalso. apply Z.eqb_neq in E. apply E. subst b. reflexivity.
  + pose proof (IH H). lia.
Qed.

Lemma jn_pre_nth : forall l k, (k < length (jn_pre l))%nat ->
  nth k (jn_pre l) 0 = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof.
induction l as [|b t IH]; intros k Hk; cbn [jn_pre] in Hk |- *; [cbn [length] in Hk; lia|].
destruct (bv_unsigned b =? 0) eqn:E; cbn [length] in Hk; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma jn_pre_zero : forall l, In (Z_to_bv 8 0) l -> bv_unsigned (nth (length (jn_pre l)) l (Z_to_bv 8 0)) = 0.
Proof.
induction l as [|b t IH]; intros H; cbn [jn_pre In] in H |- *; [destruct H|].
destruct (bv_unsigned b =? 0) eqn:E; cbn [length nth].
- apply Z.eqb_eq. exact E.
- destruct H as [H|H].
  + exfalso. apply Z.eqb_neq in E. apply E. subst b. reflexivity.
  + apply IH. exact H.
Qed.

(* ---- the model facts of a turn (address-free; over Pau's lib/Prog/Boxreg.v and
   lib/Prog/LLVMFuzzerTestOneInput_inv.v) ---- *)
(* ---- new: paste from here ---- *)
Definition jn_name (bs : list byte) (j : Z) : list Z := jn_pre (Boxreg.bx_name bs j).

Lemma jn_lnth_firstn : forall {A} (l : list A) m i d, (i < m)%nat -> nth i (firstn m l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros m i d Hi.
- destruct m; reflexivity.
- destruct m as [|m]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma jn_lnth_skipn : forall {A} (l : list A) k i d, nth i (skipn k l) d = nth (k + i)%nat l d.
Proof.
intros A l. induction l as [|x l IH]; intros k i d.
- destruct k; destruct i; reflexivity.
- destruct k as [|k]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma jn_lnth_repeat : forall {A} (a : A) m i, nth i (repeat a m) a = a.
Proof.
intros A a m. induction m as [|m IH]; intros i; destruct i as [|i]; cbn [repeat nth];
[reflexivity | reflexivity | reflexivity | apply IH].
Qed.

Lemma jn_lnth_ext : forall {A} (l l' : list A) d, length l = length l' ->
  (forall i, (i < length l)%nat -> nth i l d = nth i l' d) -> l = l'.
Proof.
intros A l. induction l as [|x l IH]; intros l' d Hl H; destruct l' as [|y l']; cbn [length] in Hl.
- reflexivity.
- lia.
- lia.
- f_equal.
  + exact (H 0%nat ltac:(cbn [length]; lia)).
  + apply (IH l' d); [lia|]. intros i Hi. exact (H (S i) ltac:(cbn [length]; lia)).
Qed.

Lemma jn_lnth_app_l : forall {A} (l l' : list A) i d, (i < length l)%nat -> nth i (l ++ l') d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros l' i d Hi; cbn [length] in Hi; [lia|].
destruct i as [|i]; [reflexivity|]. cbn [app nth]. apply IH. lia.
Qed.

Lemma jn_lnth_app_len : forall {A} (l l' : list A) d, nth (length l) (l ++ l') d = nth 0 l' d.
Proof. intros A l. induction l as [|x l IH]; intros l' d; [reflexivity|]. cbn [length app nth]. apply IH. Qed.

(* the q-th byte of the field [k, k + n) of bs is the (k + q)-th byte of bs *)
Lemma jn_bsub_nth : forall (bs : list byte) k n q d, 0 <= k -> 0 <= q < n ->
  nth (Z.to_nat q) (Boxreg.bsub bs k n) d = nth (Z.to_nat (k + q)) bs d.
Proof.
intros bs k n q d Hk Hq. unfold Boxreg.bsub. rewrite jn_lnth_firstn by lia. rewrite jn_lnth_skipn.
f_equal. lia.
Qed.

(* the C string stops before the end of its list only at a NUL byte *)
Lemma jn_pre_end : forall l, (length (jn_pre l) < length l)%nat ->
  bv_unsigned (nth (length (jn_pre l)) l (Z_to_bv 8 0)) = 0.
Proof.
induction l as [|b t IH]; intros H; [cbn [jn_pre length] in H; lia|].
revert H. cbn [jn_pre length]. destruct (bv_unsigned b =? 0) eqn:E; intros H; cbn [length nth] in H |- *.
- apply Z.eqb_eq. exact E.
- apply IH. lia.
Qed.

Lemma jn_n_small : forall bs, Boxreg.boxreg_inv bs -> 0 <= Boxreg.bx_n bs <= 5.
Proof.
intros bs HI. unfold Boxreg.boxreg_inv, Boxreg.boxreg_B16, Boxreg.boxreg_B1 in HI.
destruct HI as ((_ & H1 & _) & _). exact H1.
Qed.

Lemma jn_row_u : forall bs bs' ren j, length bs = 288%nat -> length bs' = 288%nat ->
  Boxreg.boxreg_inv bs -> LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' ren -> 0 <= j < Boxreg.bx_n bs ->
  jn_u bs' (56 * j + 8) = jn_u bs (56 * j + 8) /\ jn_u bs' (56 * j + 12) = jn_u bs (56 * j + 12) /\
  jn_u bs' (56 * j + 20) = jn_u bs (56 * j + 20).
Proof.
intros bs bs' ren j HL HL' HI HK Hj.
pose proof (jn_n_small bs HI) as H1.
unfold Boxreg.boxreg_inv, Boxreg.boxreg_B16, Boxreg.boxreg_B3, Boxreg.boxreg_B7 in HI.
destruct HI as ((_ & _ & _ & H3 & _ & _ & _) & H7).
destruct (H3 j Hj) as (_ & Hn & _ & Hb & _).
destruct (H7 j Hj) as (Hp & _).
unfold LLVMFuzzerTestOneInput_inv.llvm_kept in HK.
destruct (HK j Hj) as (Eb & En & Ep & _).
unfold Boxreg.bx_base, Boxreg.bx_nch, Boxreg.bx_pinned in *.
rewrite (jn_u_of_rd4 bs' (56 * j + 8)) by lia. rewrite (jn_u_of_rd4 bs (56 * j + 8)) by lia.
rewrite (jn_u_of_rd4 bs' (56 * j + 12)) by lia. rewrite (jn_u_of_rd4 bs (56 * j + 12)) by lia.
rewrite (jn_u_of_rd4 bs' (56 * j + 20)) by lia. rewrite (jn_u_of_rd4 bs (56 * j + 20)) by lia.
split; [exact Eb | split; [exact En | exact Ep]].
Qed.

Lemma jn_mac_zero : forall bs j, length bs = 288%nat -> 0 <= j <= 4 ->
  (Boxreg.bx_mac bs j = Boxreg.zero6 <-> forall q, 0 <= q < 6 -> jn_b bs (56 * j + q) = 0).
Proof.
intros bs j HL Hj. unfold Boxreg.bx_mac, Boxreg.zero6. split.
- intros H q Hq. unfold jn_b.
  rewrite <- (jn_bsub_nth bs (56 * j) 6 q (Z_to_bv 8 0)) by lia.
  rewrite H, jn_lnth_repeat. reflexivity.
- intros H. apply (jn_lnth_ext _ _ (Z_to_bv 8 0)).
  + rewrite Boxreg.bsub_length by lia. reflexivity.
  + intros i Hi. rewrite Boxreg.bsub_length in Hi by lia. rewrite jn_lnth_repeat.
    replace i with (Z.to_nat (Z.of_nat i)) by lia.
    rewrite (jn_bsub_nth bs (56 * j) 6 (Z.of_nat i) (Z_to_bv 8 0)) by lia.
    pose proof (H (Z.of_nat i) ltac:(lia)) as Hz. unfold jn_b in Hz.
    apply bv_eq. rewrite Hz. reflexivity.
Qed.

Lemma jn_mac_eq : forall bs bs' ren j, length bs = 288%nat -> length bs' = 288%nat ->
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' ren -> 0 <= j < Boxreg.bx_n bs -> Boxreg.bx_mac bs j <> Boxreg.zero6 ->
  forall q, 0 <= q < 6 -> jn_b bs' (56 * j + q) = jn_b bs (56 * j + q).
Proof.
intros bs bs' ren j HL HL' HK Hj Hz q Hq.
unfold LLVMFuzzerTestOneInput_inv.llvm_kept in HK.
destruct (HK j Hj) as (_ & _ & _ & [Hm|Hm] & _); [contradiction|].
unfold Boxreg.bx_mac in Hm. unfold jn_b.
rewrite <- (jn_bsub_nth bs' (56 * j) 6 q (Z_to_bv 8 0)) by lia.
rewrite <- (jn_bsub_nth bs (56 * j) 6 q (Z_to_bv 8 0)) by lia.
rewrite Hm. reflexivity.
Qed.

Lemma jn_name_nonzero : forall bs j, Forall (fun c => c <> 0) (jn_name bs j).
Proof. intros bs j. unfold jn_name. apply jn_pre_nonzero. Qed.

Lemma jn_name_len : forall bs j, length bs = 288%nat -> 0 <= j <= 4 -> Boxreg.boxreg_inv bs ->
  0 <= j < Boxreg.bx_n bs -> (length (jn_name bs j) < 32)%nat.
Proof.
intros bs j HL Hj4 HI Hj. unfold Boxreg.boxreg_inv, Boxreg.boxreg_B16, Boxreg.boxreg_B6 in HI.
destruct HI as ((_ & _ & _ & _ & _ & _ & H6) & _).
pose proof (jn_pre_len _ (H6 j Hj)) as H.
unfold jn_name. unfold Boxreg.bx_name in H |- *.
rewrite Boxreg.bsub_length in H by lia. lia.
Qed.

Lemma jn_name_bytes : forall bs j q, length bs = 288%nat -> 0 <= j <= 4 ->
  (q <= length (jn_name bs j))%nat -> (q < 32)%nat ->
  nth q (jn_name bs j ++ [0]) 0 = jn_b bs (56 * j + 24 + Z.of_nat q).
Proof.
intros bs j q HL Hj Hq Hq32. unfold jn_name, Boxreg.bx_name in *.
assert (Hl : length (Boxreg.bsub bs (56 * j + 24) 32) = 32%nat)
  by (rewrite Boxreg.bsub_length by lia; reflexivity).
assert (Hb : jn_b bs (56 * j + 24 + Z.of_nat q) =
             bv_unsigned (nth q (Boxreg.bsub bs (56 * j + 24) 32) (Z_to_bv 8 0))).
{ unfold jn_b. rewrite <- (jn_bsub_nth bs (56 * j + 24) 32 (Z.of_nat q) (Z_to_bv 8 0)) by lia.
  rewrite Nat2Z.id. reflexivity. }
rewrite Hb. set (l := Boxreg.bsub bs (56 * j + 24) 32) in *.
destruct (Nat.lt_ge_cases q (length (jn_pre l))) as [Hlt|Hge].
- rewrite (jn_lnth_app_l _ _ _ _ Hlt). apply jn_pre_nth. exact Hlt.
- assert (E : q = length (jn_pre l)) by lia. subst q.
  rewrite jn_lnth_app_len. rewrite jn_pre_end by lia. reflexivity.
Qed.

Lemma jn_name_eq : forall bs bs' ren j, length bs = 288%nat -> length bs' = 288%nat ->
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' ren -> 0 <= j < Boxreg.bx_n bs -> j <> ren ->
  jn_name bs' j = jn_name bs j.
Proof.
intros bs bs' ren j HL HL' HK Hj Hr. unfold LLVMFuzzerTestOneInput_inv.llvm_kept in HK.
destruct (HK j Hj) as (_ & _ & _ & _ & [E|E]); [contradiction|].
unfold jn_name. rewrite E. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The read-only data of this image lies below the sink's overflow head: what lib/A/Prog/BoxBase.v's
   arodata_ok_journalP needs to carry arodata_okP of the entry across the phase's calls. *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* ---- a call of a string-runtime entry inside a journal ---- *)
(* The two entries this phase calls (the bcmp and strncmp wrappers) take 2 * ESTACK of present stack below the
   caller's sp, write only inside that window and keep AR with the same ly S W; so the caller's journal is the same
   one after the call (ajournal_after_write with the window as the write set), as YC85.v's aj_intrin_atS does for
   the memcpy / memset entries. *)

Lemma jn_win_pres : forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o <= 0 -> 2 * ESTACK - o <= STK ->
  ly_stk_lo lyc + 2 * ESTACK <= spZ regsT /\
  (forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o HJ Hsp Hneg Hbud.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
pose proof Hstatic as (_ & _ & _ & Hslo & _).
split; [rewrite Eslo, Hsp; lia|].
intros a Ha. apply Hpres. rewrite Hsp in Ha. lia.
Qed.

Lemma jn_after_win : forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k mem2 md2 (o : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o <= 0 -> 2 * ESTACK - o <= STK ->
  AR SEGS B lyc Sc W mem2 md2 -> same_but_materialized mdc md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k.
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k mem2 md2 o
  HJ Hsp Hneg Hbud HAR2 Hsame Hfr Hpres2.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => spZ regsT - 2 * ESTACK <= a < spZ regsT) Sc own HJ).
- intros a Ha Hna. apply Hfr; [exact Ha | exact Hna].
- exact Hpres2.
- exact Hsame.
- intros a Ha. left. left. rewrite Hsp in Ha. lia.
- exact HAR2.
- reflexivity.
- reflexivity.
- lia.
- exact Hfrs.
- exact HQT.
Qed.

Lemma jn_bcmp_at : forall pc, abcmp_realizes SEGS B pc ->
  forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  src_ok SEGS W regsT memT x n -> src_ok SEGS W regsT memT y n ->
  (forall a, x <= a < x + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  (forall a, y <= a < y + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF y n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) y n) ->
  SRr SEGS W (cfg_at SEGS pc regsT memT mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
     (v = w64 0 <-> (forall q, 0 <= q < n -> aview SEGS (w_H W) memT (x + q) = aview SEGS (w_H W) memT (y + q))) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AB W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
  HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy Hdx Hdy Hmx Hmy Hrx Hhx Hry Hhy.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o);
  first [exact HJ | exact Hsp | exact Hal | exact Hneg | lia | (rewrite Hra; exact Hraw) | exact Hgp | exact Htp]. }
destruct (jn_win_pres W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o HJ Hsp Hneg Hbud) as [Hlo Hwp].
eapply SRr_mono.
{ exact (AB lyc Sc W regsT memT mdc x y n HPRE Hlo Hwp Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy Hdx Hdy Hmx Hmy
          Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hiff & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ exact (jn_after_win W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k mem2 md2 o
           HJ Hsp Hneg Hbud HAR2 Hsame Hfr Hpres2). }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hiff|]. split; [exact Hfr | exact Hpres2].
Qed.

Lemma jn_strncmp_at : forall pc, astrncmp_realizes SEGS B pc ->
  forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (l1 l2 : list Z) (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  fm_rom_viewN SEGS B W memT -> fm_rom_viewO SEGS B W memT ->
  fm_cstr_ok SEGS W memT x l1 -> fm_cstr_ok SEGS W memT y l2 ->
  SRr SEGS W (cfg_at SEGS pc regsT memT mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : Z),
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\ getr regs2 10 = w64 v /\ 0 <= v < 2 ^ 64 /\
     (v = 0 <-> fm_strn_eq (Z.to_nat n) l1 l2) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n l1 l2 o raw
  HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Ha1 Ha2 Hn Hrom Hclean Hc1 Hc2.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o);
  first [exact HJ | exact Hsp | exact Hal | exact Hneg | lia | (rewrite Hra; exact Hraw) | exact Hgp | exact Htp]. }
destruct (jn_win_pres W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o HJ Hsp Hneg Hbud) as [Hlo Hwp].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & _).
assert (HPREK : fm_ecall_pre_k SEGS B FM_STK_RT_STR lyc Sc W regsT memT mdc).
{ unfold fm_ecall_pre_k, FM_STK_RT_STR. split; [exact HPRE|].
  pose proof HJ as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
  split; [rewrite Eslo; unfold ASAN_CEIL; lia|]. split; [exact Hlo | exact Hwp]. }
eapply SRr_mono.
{ exact (AS lyc Sc W regsT memT mdc x y n l1 l2 HPREK Hrom Hclean Ha0 Ha1 Ha2 Hn Hc1 Hc2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hvr & Hiff & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (jn_after_win W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k mem2 md2 o
           HJ Hsp Hneg Hbud HAR2 Hsame); [|exact Hpres2].
  intros a Ha Hna. unfold FM_STK_RT_STR in Hfr. apply Hfr; [exact Ha | exact Hna]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hvr|]. split; [exact Hiff|].
split; [|exact Hpres2].
intros a Ha Hna. unfold FM_STK_RT_STR in Hfr. apply Hfr; [exact Ha | exact Hna].
Qed.

(* ---- the phase ---- *)
Variable MT : ameter_ops.
Hypothesis TL : PALib B.
Hypothesis TCHECK : tcheck_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis ASTRNCMP : astrncmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_strncmp).
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis HZB : asn_rom_bytes SEGS B (VAL (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HZ1 : IMG_LO + 64 <= VAL (A_OBJ 6).
Hypothesis HZ2 : VAL (A_OBJ 6) + 6 + 64 <= IMG_HI.
(* musl memchr's constant words, read by check's memchr wrapper (lib/A/Prog/Check.v MCH_LO / MCH_CONSTS). *)
Hypothesis HMCH : asn_rom_bytes SEGS B MCH_LO MCH_CONSTS.
(* The strncmp wrapper's view of the runtime-owned read-only statics, true in every AR state (case 0's HROMO). *)
Hypothesis HROMO : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> fm_rom_viewO SEGS B W mem.
Variable POST : bcx -> world SEGS -> config -> Prop.

Section d.
Variable cx : bcx.
Variables fp k acc : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variables r ren pos i : Z.
Variables bs bs' : list byte.
Hypothesis HB : gb_base B MT cx.
Hypothesis HLY : layout_le (length (st_secs (c_S cx))) (c_ly cx) ly3.
Hypothesis HFR : frames S3 = [(GB_CID, fp)].
Hypothesis HRIN : In (r, REG_SIZE) (ablocks B ly3 S3).
Hypothesis HBLK : gblk1 B cx ly3 S3 r.
Hypothesis HLEN : length bs = 288%nat.
Hypothesis HLEN' : length bs' = 288%nat.
Hypothesis HINV : Boxreg.boxreg_inv bs.
Hypothesis HINV' : Boxreg.boxreg_inv bs'.
Hypothesis HFAB : Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs.
Hypothesis HKEPT : LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' ren.
Hypothesis HREN : -1 <= ren < Boxreg.bx_n bs.
Hypothesis Hi : 0 <= i < 64.
Hypothesis Hk : k <= 3 + 2 * i.
Hypothesis Hacc : acc <= GB_A MT (i + 1).
Hypothesis HMO : mo_le MT (c_S cx) S3 acc.

(* The machine state the memory facts of lib/A/Prog/BoxLxDefs.v are read at: only its memory matters. *)
Definition jms (m : word -> option byte) : machine_state :=
  mkst (c_regs cx) (Z_to_bv 64 0) m (seg_rom SEGS).

(* What this phase keeps across its calls and reads back at its cuts. *)
Definition jn_mem (sh : list Z) (m : word -> option byte) : Prop :=
  gsaved cx W3 (jms m) /\ gshadow cx fp W3 (jms m) sh /\
  rdword (aview SEGS (w_H W3) m) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) /\
  gslots_fr cx fp W3 (jms m) /\ gslots_r cx fp W3 (jms m) r (Boxreg.bx_fabric bs) /\
  gcursor cx W3 (jms m) pos /\ gslot cx W3 (jms m) 0x68 i /\
  garr8 SEGS (mrestrict (w_H W3) m) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  (forall q, 0 <= q < REG_SIZE -> aview SEGS (w_H W3) m (r + q) = Some (jn_b bs' q)) /\
  gprev cx fp W3 (jms m) bs.

(* The bytes those facts speak about. *)
Definition jn_at (a : Z) : Prop :=
  c_sp1 cx <= a < 2 ^ 64 \/ c_p cx <= a < c_p cx + c_n cx \/
  gF cx fp <= a < gF cx fp + 512 \/ gSH cx fp <= a < gSH cx fp + 64 \/
  r <= a < r + REG_SIZE.
Definition jn_keep (m m' : word -> option byte) : Prop :=
  forall a, jn_at a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma jn_fin : In (GB_CID, fp) (frames S3).
Proof. rewrite HFR. left. reflexivity. Qed.

(* The geometry: the two stack pointers, the frame, its shadow and the registry block. *)
Lemma jn_sp : spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + GB_STK <= spZ (c_regs cx) /\
  spZ (c_regs cx) <= 2 ^ 47 /\ spZ (c_regs cx) - 288 < c_sp1 cx <= spZ (c_regs cx) - 256 /\
  c_sp1 cx mod 32 = 0.
Proof.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
assert (Hx : 0 <= spZ (c_regs cx) + -256) by (unfold GB_STK in *; lia).
pose proof (Z.div_mod (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hmp.
split; [exact Hal16|]. split; [unfold GB_STK in *; lia|]. split; [lia|].
split; [rewrite Hsp1; lia|].
rewrite Hsp1, Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Lemma jn_frame_addr : frame_addr ly3 GB_CID fp = gF cx fp.
Proof.
pose proof HB as (HPRE & _). pose proof HPRE as (HAR0 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HLY) as (_ & Efa & _).
unfold gF. apply Efa.
Qed.

Lemma jn_F : forall mem md, AR SEGS B ly3 S3 W3 mem md ->
  4096 <= gF cx fp /\ gF cx fp + fs_frame_bytes GB_CID <= alloc_ceiling /\
  in_app (gF cx fp) (fs_frame_bytes GB_CID) /\ gF cx fp mod 32 = 0 /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8 /\
  (forall q, 0 <= q < fs_frame_bytes GB_CID / 8 -> apresent (w_H W3) mem (gSH cx fp + q)) /\
  (forall a, gF cx fp <= a < gF cx fp + fs_frame_bytes GB_CID -> apresent (w_H W3) mem a).
Proof.
intros mem md HAR.
pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR jn_fin) as (HF0 & HFc & HFia).
destruct (al_frames _ _ LAWS _ _ _ _ _ GB_CID fp HAR jn_fin) as (Hal32 & _ & Hpr & Hsh).
rewrite jn_frame_addr in HF0, HFc, HFia, Hal32, Hpr, Hsh.
assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp) by reflexivity.
rewrite Hsa in Hsh.
split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact Hal32|].
split; [reflexivity|].
split; [intros q Hq; exact (proj1 (Hsh q Hq)) | intros a Ha; exact (proj1 (Hpr a Ha))].
Qed.

Lemma jn_sh_range : forall mem md, AR SEGS B ly3 S3 W3 mem md ->
  0 <= gSH cx fp /\ gSH cx fp + 64 <= 2 ^ 64 /\
  (forall a, gF cx fp <= a < gF cx fp + fs_frame_bytes GB_CID -> ~ (gSH cx fp <= a < gSH cx fp + 64)) /\
  gSH cx fp + 64 <= c_sp1 cx.
Proof.
intros mem md HAR.
pose proof (jn_F mem md HAR) as (HF0 & HFc & HFia & _ & HSHeq & _).
pose proof jn_sp as (_ & Hceil & H47 & Hsp1 & _).
pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
change (fs_frame_bytes GB_CID) with 512 in *.
assert (Hd1 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)) as Hmd.
unfold in_app in HFia.
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, GB_STK in *.
split; [lia|]. split; [lia|]. split; [intros a Ha; lia | lia].
Qed.

(* ---- a byte read back from a region, and the frame's shadow as chunks ---- *)
Lemma jn_val_mem1 : forall (m : word -> option byte) a v,
  aview SEGS (w_H W3) m a = Some v -> val_mem SEGS (mrestrict (w_H W3) m) a 1 v.
Proof.
intros m a v Hv j Hj.
destruct (aview_byte SEGS (w_H W3) m a v Hv) as (b & Hm & Hbv & Hr).
assert (j = 0%nat) as -> by lia. rewrite Z.add_0_r, Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r, !Z.mod_mod by lia. rewrite Z.mod_small by lia. symmetry. exact Hbv.
Qed.

Lemma jn_byte_of_region : forall (E : env) (m : word -> option byte) (n : nat) (base : Z) cs lo hi wlo whi od z v,
  YP09.region_ok SEGS E (mrestrict (w_H W3) m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = base -> In (YP09.mkChunk od (CVal 1 (SLit z))) cs ->
  zcanon z mod 256 = v ->
  aview SEGS (w_H W3) m (base + od) = Some v.
Proof.
intros E m n base cs lo hi wlo whi od z v HR Hb Hin Hv.
pose proof (field_of_region_any E (mrestrict (w_H W3) m) n base cs lo hi wlo whi od 1%N (SLit z) HR Hb Hin
  ltac:(cbn [Z.of_N]; lia)) as HM.
cbn [N.to_nat Z.of_N] in HM. change (2 ^ (8 * 1)) with 256 in HM.
assert (Hd : bv_unsigned (sv_denot E (SLit z)) = zcanon z) by (cbn [sv_denot]; apply unsigned_lit).
rewrite Hd, Hv in HM.
apply (aview_of_val_mem1 SEGS (w_H W3) m); [exact HM|].
rewrite <- Hv. apply Z.mod_pos_bound. lia.
Qed.

Lemma jn_sh_chunks_ok : forall (E : env) (m : word -> option byte) sh q,
  (forall j, (j < length sh)%nat -> aview SEGS (w_H W3) m (gSH cx fp + (q + Z.of_nat j)) = Some (nth j sh 0)) ->
  Forall (fun v => 0 <= v < 256) sh ->
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W3) m) (gSH cx fp)) (jn_sh_chunks_from q sh).
Proof.
intros E m sh. induction sh as [|v t IH]; intros q Hv Hr; cbn [jn_sh_chunks_from]; [constructor|].
assert (Hv0 : 0 <= v < 256) by (rewrite Forall_forall in Hr; apply Hr; left; reflexivity).
assert (Hrt : Forall (fun z => 0 <= z < 256) t) by (apply Forall_inv_tail in Hr; exact Hr).
constructor.
- apply (chunk_ok_val SEGS E (mrestrict (w_H W3) m) (gSH cx fp) q 1%N (SLit v) v).
  + cbn [sv_denot]. reflexivity.
  + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  + change (Z.of_N 1) with 1. lia.
  + apply jn_val_mem1. pose proof (Hv 0%nat ltac:(cbn [length]; lia)) as H0.
    cbn [nth Z.of_nat] in H0. rewrite Z.add_0_r in H0. exact H0.
- apply IH; [|exact Hrt]. intros j Hj.
  pose proof (Hv (S j) ltac:(cbn [length]; lia)) as Hj'. cbn [nth] in Hj'.
  replace (q + 1 + Z.of_nat j) with (q + Z.of_nat (S j)) by lia. exact Hj'.
Qed.

(* ---- what a call keeps, and the memory facts across it ---- *)
Lemma jn_keep_call : forall STK1 memc mdc mem2 md2 k1,
  ajournal SEGS B STK1 (c_sp1 cx) [] ly3 S3 W3 memc mdc [] ly3 S3 W3 mem2 md2 k1 ->
  jn_keep memc mem2.
Proof.
intros STK1 memc mdc mem2 md2 k1 HJ1 a Ha.
pose proof HJ1 as (HAR1 & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
pose proof HB as (_ & _ & _ & Hpn & _).
pose proof (jn_F mem2 md2 HAR1) as (HF0 & HFc & _ & _ & HSHeq & _).
pose proof jn_sp as (_ & Hceil & H47 & Hsp1 & _). unfold GB_STK in Hceil.
assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp) by reflexivity.
destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
- apply F1; lia.
- destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
  replace a with (c_p cx + (a - c_p cx)) by lia.
  apply (F2 (c_p cx) (c_n cx) (a - c_p cx) Hin3 Hin3); [lia | apply inFP_nil].
- apply (F4 GB_CID fp a jn_fin); [|apply inFP_nil].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite jn_frame_addr.
  change (fs_frame_bytes GB_CID) with 512. lia.
- apply (F4 GB_CID fp a jn_fin); [|apply inFP_nil].
  right. unfold in_zr. cbn [fst snd]. rewrite jn_frame_addr, Hsa. exact Ha.
- replace a with (r + (a - r)) by lia.
  apply (F2 r REG_SIZE (a - r) HRIN HRIN); [change (req_size REG_SIZE) with 288; unfold REG_SIZE in Ha; lia
                                           | apply inFP_nil].
Qed.

Lemma jn_rdword_keep : forall m m' a v,
  jn_keep m m' -> (forall q, 0 <= q < 8 -> jn_at (a + q)) ->
  rdword (aview SEGS (w_H W3) m) a = Some v -> rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
intros m m' a v HKP Hin Hv.
rewrite (rdword_ext (aview SEGS (w_H W3) m) (aview SEGS (w_H W3) m') a); [exact Hv|].
intros q Hq. exact (HKP (a + q) (Hin q Hq)).
Qed.

Lemma jn_mem_keep : forall sh m m', jn_mem sh m -> jn_keep m m' ->
  (length sh <= 64)%nat -> jn_mem sh m'.
Proof.
intros sh m m' HM HKP Hlen.
pose proof jn_sp as (_ & Hceil & H47 & Hsp1 & _).
pose proof HM as ((MRA & MSJ) & MSH & MFL & (MF1 & MF2 & MF3 & MF4 & MF5) &
  (MR1 & MR2 & MR3 & MR4 & MR5 & MR6) & (MC0 & MC1 & MC2) & M68 & MIN & MREG & MPREV).
assert (SLOT : forall off v, 0 <= off <= 152 -> gslot cx W3 (jms m) off v -> gslot cx W3 (jms m') off v).
{ intros off v Hoff Hs. unfold gslot, jms in *. cbn [ms_mem mkst] in *.
  apply (jn_rdword_keep m m' _ _ HKP); [intros q Hq; left; lia | exact Hs]. }
unfold jn_mem, gsaved, gshadow, gslots_fr, gslots_r, gcursor, gprev, jms in *.
cbn [ms_mem mkst] in *.
split.
{ split.
  - apply (jn_rdword_keep m m' _ _ HKP); [intros q Hq; left; lia | exact MRA].
  - intros j Hj. apply (jn_rdword_keep m m' _ _ HKP); [intros q Hq; left; lia | exact (MSJ j Hj)]. }
split.
{ intros j Hj. rewrite (HKP (gSH cx fp + Z.of_nat j)); [exact (MSH j Hj)|].
  right; right; right; left. change (fs_frame_bytes GB_CID / 8) with 64. lia. }
split.
{ apply (jn_rdword_keep m m' _ _ HKP); [|exact MFL].
  intros q Hq. right; right; left. change (fs_frame_bytes GB_CID) with 512. lia. }
split.
{ split; [apply (SLOT 0x18); [lia | exact MF1]|]. split; [apply (SLOT 0x28); [lia | exact MF2]|].
  split; [apply (SLOT 0x70); [lia | exact MF3]|]. split; [apply (SLOT 0x78); [lia | exact MF4]|].
  apply (SLOT 0x80); [lia | exact MF5]. }
split.
{ split; [apply (SLOT 0x10); [lia | exact MR1]|]. split; [apply (SLOT 0x20); [lia | exact MR2]|].
  split; [apply (SLOT 0x38); [lia | exact MR3]|]. split; [apply (SLOT 0x40); [lia | exact MR4]|].
  split; [apply (SLOT 0x50); [lia | exact MR5]|]. apply (SLOT 0x60); [lia | exact MR6]. }
split.
{ split; [exact MC0|]. split; [apply (SLOT 0x88); [lia | exact MC1]|]. apply (SLOT 0x90); [lia | exact MC2]. }
split; [apply (SLOT 0x68); [lia | exact M68]|].
split.
{ apply (garr8_frame SEGS _ _ _ _ MIN). intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview SEGS). apply HKP. right; left. unfold c_n. lia. }
split.
{ intros q Hq. rewrite (HKP (r + q)); [exact (MREG q Hq)|]. right; right; right; right. unfold REG_SIZE in *. lia. }
intros q Hq. rewrite (HKP (gF cx fp + GO_PREV + q)); [exact (MPREV q Hq)|].
right; right; left. change (fs_frame_bytes GB_CID) with 512. unfold GO_PREV, REG_SIZE in *. lia.
Qed.

Lemma jn_app_apart : forall a n q, in_app a n -> 0 <= q < n ->
  forall mem md, AR SEGS B ly3 S3 W3 mem md -> ~ (gSH cx fp <= a + q < gSH cx fp + 64).
Proof.
intros a n q Hin Hq mem md HAR.
pose proof (jn_F mem md HAR) as (HF0 & HFc & _ & _ & HSHeq & _).
pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
change (fs_frame_bytes GB_CID) with 512 in *.
assert (Hd1 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)) as Hmd.
unfold in_app in Hin.
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Lemma jn_GSH_it_range : Forall (fun z => 0 <= z < 256) GSH_it.
Proof.
unfold GSH_it. apply Forall_app. split; [repeat (apply Forall_cons; [lia|]); apply Forall_nil|].
apply Forall_app. split; apply Forall_forall; intros z Hz; apply repeat_spec in Hz; subst z; lia.
Qed.

Lemma jn_GSH_J_range : Forall (fun z => 0 <= z < 256) GSH_J.
Proof.
unfold GSH_J. apply Forall_app. split; [repeat (apply Forall_cons; [lia|]); apply Forall_nil|].
apply Forall_app. split; apply Forall_forall; intros z Hz; apply repeat_spec in Hz; subst z; lia.
Qed.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The one write window of the re-poisoning block: the frame's shadow bytes, inside [0, 64) at s8. *)
Lemma jn_awr_tail : forall (E : env) (rs : YP09.smem),
  bv_unsigned (ew E 24) = gSH cx fp ->
  (forall rg, In rg rs -> YP09.r_whi rg <= YP09.r_wlo rg \/
     (YP09.r_base rg = Some 24%nat /\ 0 <= YP09.r_wlo rg /\ YP09.r_whi rg <= 64)) ->
  awr_ok E rs GB_STK (spZ (c_regs cx)) []
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(GB_CID, fp)].
Proof.
intros E rs HU24 Hrs a (rg & Hin & Hb).
destruct (Hrs rg Hin) as [Hro | (Hbase & Hlo & Hhi)]; [lia|].
rewrite Hbase in Hb. cbn [YP09.base_val] in Hb. rewrite HU24 in Hb.
right; right; right. exists GB_CID, fp. split; [left; reflexivity|]. right.
unfold in_zr. cbn [fst snd]. rewrite jn_frame_addr.
unfold shadow_addr, gSH, shadow_of_addr in *. change (fs_frame_bytes GB_CID / 8) with 64. lia.
Qed.

Ltac jn_awr U24 :=
  apply jn_awr_tail; [exact U24 | intros rg Hin; vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi];
       solve [left; lia | right; split; [reflexivity | split; lia]] |]);
    exfalso; exact Hin].

(* A byte the re-poisoning block did not write is the byte the phase brought in. *)
Lemma jn_keep_outside : forall (E : env) rs (m m' : word -> option byte) a,
  frame_of E rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
intros E rs m m' a HF Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

Lemma jn_keep_outside_raw : forall (E : env) rs (m m' : word -> option byte) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
intros E rs m m' a HF Ha Hn. unfold aview, mbyte, mrestrict.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

(* ---- the frame's objects, while they are in scope ---- *)
Lemma jn_nth_repeat : forall (v d : Z) m q, (q < m)%nat -> nth q (repeat v m) d = v.
Proof.
intros v d m. induction m as [|m IH]; intros q Hq; [lia|].
destruct q as [|q]; cbn [repeat nth]; [reflexivity | apply IH; lia].
Qed.

Lemma jn_GSH_it_mid : forall q, (8 <= q < 44)%nat -> nth q GSH_it 0 = 0.
Proof.
intros q Hq. unfold GSH_it.
rewrite app_nth2 by (cbn [length]; lia). cbn [length].
rewrite app_nth1 by (rewrite repeat_length; lia).
apply jn_nth_repeat. lia.
Qed.

Lemma jn_apresent_aview : forall (m : word -> option byte) a,
  apresent (w_H W3) m a -> aview SEGS (w_H W3) m a <> None.
Proof.
intros m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* A byte of the frame that is in scope inside a turn (mac and prev) has shadow 0. *)
Lemma jn_frame_sh0 : forall (m : word -> option byte) md2 (c : Z),
  AR SEGS B ly3 S3 W3 m md2 ->
  gshadow cx fp W3 (jms m) GSH_it -> 64 <= c < 352 ->
  aview SEGS (w_H W3) m (shadow_of_addr SHADOW_OFF (gF cx fp + c)) = Some 0.
Proof.
intros m md2 c HAR HSH Hc.
assert (Hg8 : gF cx fp mod 8 = 0).
{ pose proof (jn_F m md2 HAR) as (_ & _ & _ & H32 & _).
  apply Z.mod_divide in H32; [|lia]. apply Z.mod_divide; [lia|].
  destruct H32 as [q Hq]. exists (4 * q). lia. }
rewrite (shadow_of_addr_aligned_off SHADOW_OFF (gF cx fp) c Hg8).
replace (shadow_of_addr SHADOW_OFF (gF cx fp)) with (gSH cx fp) by reflexivity.
pose proof (HSH (Z.to_nat (c / 8)) ltac:(vm_compute (length GSH_it);
  pose proof (Z.div_le_mono 64 c 8 ltac:(lia)); pose proof (Z.div_lt_upper_bound c 8 44 ltac:(lia) ltac:(lia)); lia))
  as HQ.
unfold jms in HQ. cbn [ms_mem mkst] in HQ.
rewrite Z2Nat.id in HQ by (apply Z.div_pos; lia).
rewrite HQ, jn_GSH_it_mid; [reflexivity|].
pose proof (Z.div_le_mono 64 c 8 ltac:(lia)). pose proof (Z.div_lt_upper_bound c 8 44 ltac:(lia) ltac:(lia)).
change (64 / 8) with 8 in *. lia.
Qed.

Lemma jn_frame_ra : forall (m : word -> option byte) md2 a n,
  AR SEGS B ly3 S3 W3 m md2 ->
  gshadow cx fp W3 (jms m) GSH_it -> gF cx fp + 64 <= a -> a + n <= gF cx fp + 352 -> 0 <= n ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF a n.
Proof.
intros m md2 a n HAR HSH Ha Han Hn x Hx. exists 0. split; [|left; reflexivity].
replace x with (gF cx fp + (x - gF cx fp)) by lia.
apply (jn_frame_sh0 m md2 (x - gF cx fp) HAR HSH). lia.
Qed.

Lemma jn_sh_off : forall c, gF cx fp mod 8 = 0 ->
  SHADOW_OFF + (gF cx fp + c) / 8 = gSH cx fp + c / 8.
Proof.
intros c Hg8.
change (SHADOW_OFF + (gF cx fp + c) / 8) with (shadow_of_addr SHADOW_OFF (gF cx fp + c)).
rewrite (shadow_of_addr_aligned_off SHADOW_OFF (gF cx fp) c Hg8). reflexivity.
Qed.

Lemma jn_frame_hull : forall (m : word -> option byte) md2 a n,
  AR SEGS B ly3 S3 W3 m md2 ->
  gF cx fp + 64 <= a -> a + n <= gF cx fp + 352 -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W3) m) a n.
Proof.
intros m md2 a n HAR Ha Han Hn s Hs.
pose proof (jn_F m md2 HAR) as (HF0 & HFc & _ & H32 & HSHeq & HP & _).
change (fs_frame_bytes GB_CID / 8) with 64 in HP.
assert (Hg8 : gF cx fp mod 8 = 0).
{ apply Z.mod_divide in H32; [|lia]. apply Z.mod_divide; [lia|].
  destruct H32 as [q Hq]. exists (4 * q). lia. }
assert (E1 : shadow_addr a = gSH cx fp + (a - gF cx fp) / 8).
{ unfold shadow_addr. rewrite <- (jn_sh_off (a - gF cx fp) Hg8). f_equal. f_equal. lia. }
assert (E2 : shadow_addr (a + n - 1) = gSH cx fp + (a + n - 1 - gF cx fp) / 8).
{ unfold shadow_addr. rewrite <- (jn_sh_off (a + n - 1 - gF cx fp) Hg8). f_equal. f_equal. lia. }
rewrite E1, E2 in Hs.
pose proof (Z.div_le_mono 64 (a - gF cx fp) 8 ltac:(lia)) as D1.
pose proof (Z.div_lt_upper_bound (a + n - 1 - gF cx fp) 8 44 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_pos (a - gF cx fp) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_pos (a + n - 1 - gF cx fp) 8 ltac:(lia) ltac:(lia)) as D4.
change (64 / 8) with 8 in D1.
pose proof (Z.mul_div_le (gSH cx fp + (a - gF cx fp) / 8) 8 ltac:(lia)) as D5.
pose proof (Z.mod_pos_bound (gSH cx fp + (a + n - 1 - gF cx fp) / 8) 8 ltac:(lia)) as D6.
pose proof (Z.div_mod (gSH cx fp + (a + n - 1 - gF cx fp) / 8) 8 ltac:(lia)) as D7.
pose proof (Z.mod_pos_bound (gSH cx fp + (a - gF cx fp) / 8) 8 ltac:(lia)) as D8.
pose proof (Z.div_mod (gSH cx fp + (a - gF cx fp) / 8) 8 ltac:(lia)) as D9.
apply jn_apresent_aview. replace s with (gSH cx fp + (s - gSH cx fp)) by lia.
apply HP. lia.
Qed.

(* ---- the registry block's shadow, the image's ZERO, and the call window ---- *)
Lemma jn_hull_sub : forall (rd : Z -> option Z) p n a m,
  shadow_hull_vis rd p n -> p <= a -> 0 < m -> a + m <= p + n -> shadow_hull_vis rd a m.
Proof.
intros rd p n a m HV Hpa Hm Ham s Hs. apply HV.
pose proof (shadow_mono p a Hpa) as M1.
pose proof (shadow_mono (a + m - 1) (p + n - 1) ltac:(lia)) as M2.
pose proof (Z.mul_div_le (shadow_addr p) 8 ltac:(lia)) as D1.
pose proof (Z.div_mod (shadow_addr p) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (shadow_addr p) 8 ltac:(lia)) as D3.
pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)) as D5.
pose proof (Z.div_le_mono (shadow_addr p) (shadow_addr a) 8 ltac:(lia) M1) as D6.
pose proof (Z.div_le_mono (shadow_addr (a + m - 1)) (shadow_addr (p + n - 1)) 8 ltac:(lia) M2) as D7.
lia.
Qed.

Lemma jn_blk_sh : forall (m : word -> option byte) md2 a n,
  AR SEGS B ly3 S3 W3 m md2 -> r <= a -> a + n <= r + REG_SIZE -> 0 < n ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF a n /\
  shadow_hull_vis (aview SEGS (w_H W3) m) a n.
Proof.
intros m md2 a n HAR Ha Han Hn.
destruct (al_shadow _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (HBS & HHV).
change (req_size REG_SIZE) with 288 in HBS, HHV. unfold REG_SIZE in Han.
split.
- apply (block_shadow_range (aview SEGS (w_H W3) m) SHADOW_OFF r 288 a n HBS); lia.
- apply (jn_hull_sub _ r 288 a n HHV); lia.
Qed.

Lemma jn_zero_bytes : forall (m : word -> option byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) m) ->
  forall q, 0 <= q < 6 -> aview SEGS (w_H W3) m (VAL (A_OBJ 6) + q) = Some 0.
Proof.
intros m HRO q Hq.
destruct (HZB q ltac:(rewrite length_map; cbn [length Boxreg.zero6 repeat]; lia))
  as (Hrom & Hown & Herr & Hb).
rewrite (HRO (VAL (A_OBJ 6) + q) (or_introl Hrom) Hown Herr), Hb.
f_equal. unfold Boxreg.zero6.
assert (Hm : map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 6) = repeat 0 6) by reflexivity.
rewrite Hm. apply jn_nth_repeat. lia.
Qed.

Lemma jn_zero_sh : forall (m : word -> option byte) md2,
  AR SEGS B ly3 S3 W3 m md2 ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (VAL (A_OBJ 6)) 6 /\
  shadow_hull_vis (aview SEGS (w_H W3) m) (VAL (A_OBJ 6)) 6.
Proof.
intros m md2 HAR.
destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 m md2 (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
  HGLOB ltac:(unfold BX_G; left; reflexivity) HISV HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia)) as [HRA HHV].
split; [exact HRA | exact HHV].
Qed.

(* The call window of the string runtime entries, and the offset of the realigned stack pointer. *)
Lemma jn_off : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0 /\ c_sp1 cx - spZ (c_regs cx) <= 0 /\
  2 * ESTACK - (c_sp1 cx - spZ (c_regs cx)) <= GB_STK.
Proof.
pose proof jn_sp as (Hal16 & Hceil & H47 & Hsp1 & Hsp32).
split.
{ apply Z.mod_divide; [lia|].
  apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hsp32; [|lia].
  destruct Hal16 as [q1 Hq1]. destruct Hsp32 as [q2 Hq2]. exists (2 * q2 - q1). lia. }
split; [lia|]. unfold ESTACK, GB_STK. lia.
Qed.

(* ---- the premises of the three interceptor calls of a turn ---- *)
Lemma jn_app_range : forall a n, in_app a n -> 0 <= n -> 4096 <= a /\ a + n <= ASAN_CEIL /\ amem_range a n.
Proof.
intros a n Ha Hn. pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
unfold in_app in Ha. unfold amem_range, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *.
destruct Ha as (H1 & [H2 | [H2 H3]]); (split; [lia|]); (split; [lia|]); [left; lia | right; lia].
Qed.

(* prev's row j, and r's row j: the bytes the bcmp / strncmp wrappers read. *)
Lemma jn_prev_ok : forall (m : word -> option byte) md2 (regsT : bvmap 5 word) p n,
  AR SEGS B ly3 S3 W3 m md2 -> jn_mem GSH_it m -> spZ regsT = c_sp1 cx ->
  gF cx fp + 64 <= p -> 0 < n -> p + n <= gF cx fp + 352 ->
  src_ok SEGS W3 regsT m p n /\
  (forall a, p <= a < p + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
  amem_range p n /\ 0 <= p /\ p + n <= 2 ^ 63 /\
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF p n /\
  shadow_hull_vis (aview SEGS (w_H W3) m) p n.
Proof.
intros m md2 regsT p n HAR HM Hsp Hc Hn Hcn.
pose proof (jn_F m md2 HAR) as (HF0 & HFc & HFia & _ & _ & HSHp & _).
pose proof jn_sp as (_ & Hceil & H47 & Hsp1 & _). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & _).
pose proof HM as (_ & MSH & _ & _ & _ & _ & _ & _ & _ & MPREV).
change (fs_frame_bytes GB_CID) with 512 in *.
destruct (jn_app_range (gF cx fp) 512 HFia ltac:(lia)) as (HA1 & HA2 & _).
assert (HSUB : in_app p n)
  by (apply (in_app_sub (gF cx fp) 512); [exact HFia | lia | lia | lia]).
destruct (jn_app_range p n HSUB ltac:(lia)) as (HB1 & HB2 & HB3).
assert (HBY : forall a, p <= a < p + n -> aview SEGS (w_H W3) m a <> None).
{ intros a Ha. unfold gprev, jms in MPREV. cbn [ms_mem mkst] in MPREV.
  replace a with (gF cx fp + GO_PREV + (a - gF cx fp - GO_PREV)) by (unfold GO_PREV; lia).
  rewrite (MPREV (a - gF cx fp - GO_PREV) ltac:(unfold GO_PREV, REG_SIZE; lia)). discriminate. }
split; [intros a Ha; split; [exact (HBY a Ha) | unfold ESTACK, ASAN_CEIL in *; lia]|].
split; [intros a Ha; unfold ESTACK, ASAN_CEIL in *; lia|].
split; [exact HB3|].
split; [lia|]. split; [unfold ASAN_CEIL in *; lia|].
split.
- apply (jn_frame_ra m md2 _ _ HAR MSH); lia.
- apply (jn_frame_hull m md2 _ _ HAR); lia.
Qed.

Lemma jn_reg_ok : forall (m : word -> option byte) md2 (regsT : bvmap 5 word) p n,
  AR SEGS B ly3 S3 W3 m md2 -> jn_mem GSH_it m -> spZ regsT = c_sp1 cx ->
  r <= p -> 0 < n -> p + n <= r + REG_SIZE ->
  src_ok SEGS W3 regsT m p n /\
  (forall a, p <= a < p + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
  amem_range p n /\ 0 <= p /\ p + n <= 2 ^ 63 /\
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF p n /\
  shadow_hull_vis (aview SEGS (w_H W3) m) p n.
Proof.
intros m md2 regsT p n HAR HM Hsp Hc Hn Hcn.
pose proof jn_sp as (_ & Hceil & H47 & Hsp1 & _). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & MREG & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (_ & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria. unfold REG_SIZE in Hcn.
assert (HSUB : in_app p n) by (apply (in_app_sub r 288); [exact Hria | lia | lia | lia]).
destruct (jn_app_range p n HSUB ltac:(lia)) as (HB1 & HB2 & HB3).
assert (HBY : forall a, p <= a < p + n -> aview SEGS (w_H W3) m a <> None).
{ intros a Ha. replace a with (r + (a - r)) by lia.
  rewrite (MREG (a - r) ltac:(unfold REG_SIZE in *; lia)). discriminate. }
split; [intros a Ha; split; [exact (HBY a Ha) | unfold ESTACK, ASAN_CEIL in *; lia]|].
split; [intros a Ha; unfold ESTACK, ASAN_CEIL in *; lia|].
split; [exact HB3|]. split; [lia|]. split; [unfold ASAN_CEIL in *; lia|].
apply (jn_blk_sh m md2 p n HAR); unfold REG_SIZE in *; lia.
Qed.

Lemma jn_zero_ok : forall (m : word -> option byte) md2 (regsT : bvmap 5 word),
  AR SEGS B ly3 S3 W3 m md2 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) m) -> spZ regsT = c_sp1 cx ->
  src_ok SEGS W3 regsT m (VAL (A_OBJ 6)) 6 /\
  (forall a, VAL (A_OBJ 6) <= a < VAL (A_OBJ 6) + 6 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
  amem_range (VAL (A_OBJ 6)) 6 /\ 0 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 6 <= 2 ^ 63 /\
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (VAL (A_OBJ 6)) 6 /\
  shadow_hull_vis (aview SEGS (w_H W3) m) (VAL (A_OBJ 6)) 6.
Proof.
intros m md2 regsT HAR HRO Hsp.
pose proof jn_sp as (_ & Hceil & H47 & Hsp1 & _). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
pose proof (jn_zero_bytes m HRO) as HZ.
destruct (jn_zero_sh m md2 HAR) as [HRA HHV].
unfold IMG_HI in HZ2.
split; [intros a Ha; split;
  [replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia; rewrite (HZ (a - VAL (A_OBJ 6)) ltac:(lia));
   discriminate | unfold ESTACK, ASAN_CEIL in *; lia]|].
split; [intros a Ha; unfold ESTACK, ASAN_CEIL in *; lia|].
split; [unfold amem_range, kLowMemEnd; left; lia|].
split; [lia|]. split; [lia|]. split; [exact HRA | exact HHV].
Qed.

(* A 4-byte field of a 288-byte struct, as the engine reads it. *)
Lemma jn_val4 : forall (m : word -> option byte) p (bsX : list byte) off,
  (forall q, 0 <= q < REG_SIZE -> aview SEGS (w_H W3) m (p + q) = Some (jn_b bsX q)) ->
  0 <= off -> off + 4 <= REG_SIZE ->
  val_mem SEGS (mrestrict (w_H W3) m) (p + off) (N.to_nat 4) (jn_u bsX off).
Proof.
intros m p bsX off Hb H0 H1. unfold val_mem. intros q Hq. change (N.to_nat 4) with 4%nat in Hq |- *.
rewrite le_byte_small by (pose proof (jn_u_range bsX off);
  first [lia | (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia)]).
destruct (aview_byte SEGS (w_H W3) m (p + (off + Z.of_nat q)) _
  (Hb (off + Z.of_nat q) ltac:(unfold REG_SIZE in *; lia))) as (b & Hbm & Hv & _).
replace (p + off + Z.of_nat q) with (p + (off + Z.of_nat q)) by lia. rewrite Hbm. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. rewrite (jn_u_byte bsX off q Hq). symmetry. exact Hv.
Qed.

(* The shadow address the turn's cursor s10 holds. *)
Lemma jn_U_shadow : forall (E' : env) (n : nat) (v c sb : Z),
  ew E' n = w64 v -> ew E' 18 = w64 sb -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 -> 0 <= sb ->
  sb + (v + c) / 8 < 2 ^ 64 ->
  sv_denot E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 18%nat 0)) =
  w64 (sb + (v + c) / 8).
Proof.
intros E' n v c sb H20 H18 Hv Hc Hvc Hsb Hsum.
assert (Hd : 0 <= (v + c) / 8 <= v + c)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite U_srl3, !U_SOff, H20, H18.
rewrite !unsigned_lit_small by lia.
rewrite Z.add_0_r.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite (zcanon_id ((v + c) / 8 + sb)) by (unfold M64; lia). unfold w64. f_equal. lia.
Qed.

(* The cut's memory facts at the end of the block: the 37 bytes the block wrote turn GSH_it into GSH_J, and every
   other byte the phase speaks about is where it was. *)
Lemma jn_land_mem : forall (msF : machine_state) (mem mem2 : word -> option byte) md2,
  AR SEGS B ly3 S3 W3 mem2 md2 ->
  jn_mem GSH_it mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (gSH cx fp + 4 <= a < gSH cx fp + 44) ->
     aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem a) ->
  (forall q, (q < 52)%nat -> aview SEGS (w_H W3) (ms_mem msF) (gSH cx fp + Z.of_nat q) = Some (nth q GSH_J 0)) ->
  jn_mem GSH_J (ms_mem msF).
Proof.
intros msF mem mem2 md2 HAR HM KOUT KSH.
pose proof (jn_F mem2 md2 HAR) as (HF0 & HFc & HFia & _ & HSHeq & _).
pose proof (jn_sh_range mem2 md2 HAR) as (HS0 & HS1 & HSdF & HSdsp).
pose proof jn_sp as (Hal16 & Hceil & H47 & Hsp1 & Hsp32). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & _).
change (fs_frame_bytes GB_CID) with 512 in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (_ & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
pose proof HB as (_ & _ & _ & Hpn & _).
assert (KIN : forall a, c_p cx <= a < c_p cx + c_n cx ->
  aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem a).
{ intros a Ha. destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & Hpia & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
  apply KOUT; [lia|].
  pose proof (jn_app_apart (c_p cx) (req_size (c_n cx)) (a - c_p cx) Hpia ltac:(lia) mem2 md2 HAR).
  replace (c_p cx + (a - c_p cx)) with a in * by lia. lia. }
assert (KR : forall q, 0 <= q < REG_SIZE -> aview SEGS (w_H W3) (ms_mem msF) (r + q) = aview SEGS (w_H W3) mem (r + q)).
{ intros q Hq. apply KOUT; [unfold REG_SIZE in Hq; lia|].
  pose proof (jn_app_apart r 288 q Hria ltac:(unfold REG_SIZE in Hq; lia) mem2 md2 HAR). lia. }
assert (KF : forall q, 0 <= q < 512 ->
  aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + q) = aview SEGS (w_H W3) mem (gF cx fp + q)).
{ intros q Hq. apply KOUT; [lia|].
  pose proof (HSdF (gF cx fp + q) ltac:(lia)). lia. }
assert (KS : forall off, 0 <= off <= 152 -> forall v, gslot cx W3 (jms mem) off v -> gslot cx W3 (jms (ms_mem msF)) off v).
{ intros off Hoff v Hv. unfold gslot, jms in *. cbn [ms_mem mkst] in *.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem msF))); [exact Hv|].
  intros q Hq. apply KOUT; lia. }
pose proof HM as ((MRA & MSJ) & MSH & MFL & (MF1 & MF2 & MF3 & MF4 & MF5) &
  (MR1 & MR2 & MR3 & MR4 & MR5 & MR6) & (MC0 & MC1 & MC2) & M68 & MIN & MREG & MPREV).
unfold jn_mem, gsaved, gshadow, gslots_fr, gslots_r, gcursor, gprev, jms in *.
cbn [ms_mem mkst] in *.
split.
{ split.
  - rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem msF))); [exact MRA|].
    intros q Hq. apply KOUT; lia.
  - intros j Hj.
    rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem msF))); [exact (MSJ j Hj)|].
    intros q Hq. apply KOUT; lia. }
split; [intros j Hj; apply KSH; revert Hj; vm_compute (length GSH_J); auto|].
split.
{ rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem msF))); [exact MFL|].
  intros q Hq. change (fs_frame_bytes GB_CID) with 512.
  replace (gF cx fp + 512 - 8 + q) with (gF cx fp + (504 + q)) by lia. apply KF. lia. }
split.
{ split; [exact (KS 0x18 ltac:(lia) _ MF1)|]. split; [exact (KS 0x28 ltac:(lia) _ MF2)|].
  split; [exact (KS 0x70 ltac:(lia) _ MF3)|]. split; [exact (KS 0x78 ltac:(lia) _ MF4)|].
  exact (KS 0x80 ltac:(lia) _ MF5). }
split.
{ split; [exact (KS 0x10 ltac:(lia) _ MR1)|]. split; [exact (KS 0x20 ltac:(lia) _ MR2)|].
  split; [exact (KS 0x38 ltac:(lia) _ MR3)|]. split; [exact (KS 0x40 ltac:(lia) _ MR4)|].
  split; [exact (KS 0x50 ltac:(lia) _ MR5)|]. exact (KS 0x60 ltac:(lia) _ MR6). }
split.
{ split; [exact MC0|]. split; [exact (KS 0x88 ltac:(lia) _ MC1)|]. exact (KS 0x90 ltac:(lia) _ MC2). }
split; [exact (KS 0x68 ltac:(lia) _ M68)|].
split.
{ apply (garr8_frame SEGS _ _ _ _ MIN). intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview SEGS). apply KIN. unfold c_n. lia. }
split.
{ intros q Hq. rewrite (KR q Hq). exact (MREG q Hq). }
intros q Hq.
replace (gF cx fp + GO_PREV + q) with (gF cx fp + (GO_PREV + q)) by lia.
rewrite (KF (GO_PREV + q) ltac:(unfold GO_PREV, REG_SIZE in *; lia)).
replace (gF cx fp + (GO_PREV + q)) with (gF cx fp + GO_PREV + q) by lia. exact (MPREV q Hq).
Qed.

(* `addiw s5, s5, 1` on the turn counter. *)
Lemma jn_U_addiw : forall (E' : env) (n : nat) (v : Z), ew E' n = w64 v -> 0 <= v < 2 ^ 30 ->
  U E' (SAluw ALU_ADD (SOff n 0) (SLit 1)) = v + 1.
Proof.
intros E' n v Hn Hv.
rewrite U_of_S, S_SAluw, U_SOff, U_SLit, Hn, Z.add_0_r.
rewrite unsigned_lit_small by lia.
unfold zcanon, M64. rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
rewrite (Z.mod_small v (2 ^ 32)) by lia. rewrite (Z.mod_small 1 (2 ^ 32)) by lia.
cbn [zalu_raw].
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
change (2 ^ 32 / 2) with (2 ^ 31).
rewrite (Z.mod_small (v + 1 + 2 ^ 31) (2 ^ 32)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.

Ltac jn_in_chunk := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma jn_tail :
  (i + 1 < 64 -> gb_from B MT POST (GI_J B MT (i + 1))) ->
  gb_from B MT POST (GI_X B MT) ->
  forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 24 = w64 (gSH cx fp) -> getr regs 20 = w64 r ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 mem md k ->
  jn_mem GSH_it mem ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + JP_sh)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
intros HJN HXN regs mem md G2 G8 G9 G3 G4 G18 G24 G20 HJ HM.
pose proof HJ as (HAR & _).
pose proof (jn_F mem md HAR) as (HF0 & HFc & HFia & HF32 & HSHeq & HSHp & HFp).
pose proof (jn_sh_range mem md HAR) as (HS0 & HS1 & HSdF & HSdsp).
pose proof jn_sp as (Hal16 & Hceil & H47 & Hsp1 & Hsp32). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof HM as (MSV & MSH & MFL & MFR & MSR & MCUR & M68 & MIN & MREG & MPREV).
pose proof MSR as (MR10 & MR20 & MR38 & MR40 & MR50 & MR60).
pose proof HINV as ((HLb & HB1 & HB2 & _) & _).
unfold Boxreg.boxreg_B2 in HB2.
set (E := Eimg (Ereg regs [w64 (Boxreg.bx_fabric bs); w64 i])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
  by (intros q rr Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (F32 : ew E 32 = w64 (Boxreg.bx_fabric bs))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (F33 : ew E 33 = w64 i)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = gSH cx fp)
  by (rewrite (EE 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E jn_ss_tail
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + JP_sh)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold jn_ss_tail. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold jn_R_slots_tail, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) (c_sp1 cx) 0x50 8%N (SOff 32%nat 0)
                 (Boxreg.bx_fabric bs)).
        -- cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- change (Z.of_N 8) with 8. lia.
        -- apply (val_mem_of_rdword SEGS (w_H W3) mem). exact MR50.
      * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) (c_sp1 cx) 0x68 8%N (SOff 33%nat 0) i).
        -- cbn [sv_denot]. rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- change (Z.of_N 8) with 8. lia.
        -- apply (val_mem_of_rdword SEGS (w_H W3) mem). exact M68.
    + unfold jn_R_sh, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U24. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HSHp;
              change (fs_frame_bytes GB_CID / 8) with 64; lia|].
      apply (jn_sh_chunks_ok E mem GSH_it 0); [|exact jn_GSH_it_range].
      intros j Hj. replace (0 + Z.of_nat j) with (Z.of_nat j) by lia. exact (MSH j Hj).
  - apply pairwise_disjoint_of_extents.
    unfold jn_R_slots_tail, jn_R_sh, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
    rewrite U9, U24. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I. lia.
  - split; [|split; exact I]. cbn [jn_AF_sh f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24.
    split; [unfold gSH, shadow_of_addr, SHADOW_OFF in *; lia|].
    split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
assert (SHOK : sh_ok SEGS JBx [] E (mrestrict (w_H W3) mem)) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK JBspan; [jn_awr U24 |].
psrr_branch_tok RUN BR HS SHOK JBspan.
- (* i + 1 <> 64: the back edge at 0x80ce8 to the loop head 0x801ec *)
  rewrite branch_ne_U, (jn_U_addiw E 33%nat i F33 ltac:(lia)), U_SLit in Hc.
  change (zcanon 64) with 64 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK JBspan GP_J; [jn_awr U24 |].
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
  assert (KOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (gSH cx fp + 4 <= a < gSH cx fp + 44) ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem a).
  { intros a Ha Hn.
    repeat match goal with
    | HFx : frame_of ?Ex ?rsx ?m1 ?m2 |- _ =>
        let Hq := fresh "KQ" in
        assert (Hq : aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem msF) a) by reflexivity;
        clear Hq;
        first
        [ (let Hq := fresh "KQ" in
           assert (Hq : aview SEGS (w_H W3) m2 a = aview SEGS (w_H W3) m1 a)
             by (first [ apply (jn_keep_outside Ex rsx _ _ a HFx Ha)
                       | apply (jn_keep_outside_raw Ex rsx m1 m2 a HFx Ha) ];
                 intros (rg & Hin & Hb); vm_compute in Hin;
                 repeat (destruct Hin as [<- | Hin];
                   [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb;
                    try rewrite U24 in Hb; try rewrite U9 in Hb; lia |]);
                 exact Hin);
           clear HFx; try rewrite Hq; clear Hq)
        | clear HFx ]
    end; reflexivity. }
  pose proof (st_ok_pi_region_nth E _ (restrict (w_H W3) msF) 1%nat _ HS eq_refl) as Rsh.
  cbn [restrict ms_mem mkst] in Rsh.
  assert (SHJ : forall q, 0 <= q < 52 ->
    aview SEGS (w_H W3) (ms_mem msF) (gSH cx fp + q) = Some (nth (Z.to_nat q) GSH_J 0)).
  { intros q Hq. assert (Hcase : q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 11 \/ q = 12 \/ q = 13 \/ q = 14 \/ q = 15 \/ q = 16 \/ q = 17 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27 \/ q = 28 \/ q = 29 \/ q = 30 \/ q = 31 \/ q = 32 \/ q = 33 \/ q = 34 \/ q = 35 \/ q = 36 \/ q = 37 \/ q = 38 \/ q = 39 \/ q = 40 \/ q = 41 \/ q = 42 \/ q = 43 \/ q = 44 \/ q = 45 \/ q = 46 \/ q = 47 \/ q = 48 \/ q = 49 \/ q = 50 \/ q = 51) by lia.
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    rewrite Hcase.
    eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity]. }
  assert (HMJ : jn_mem GSH_J (ms_mem msF)).
  { apply (jn_land_mem msF mem (ms_mem msF) _ (proj1 HJ) HM KOUT).
    intros q Hq.
    assert (Hq52 : (q < 52)%nat) by (revert Hq; vm_compute (length GSH_J); lia).
    pose proof (SHJ (Z.of_nat q) ltac:(lia)) as HSq. rewrite Nat2Z.id in HSq. exact HSq. }
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  rewrite (EE 2%nat 2%bv eq_refl) in Q2. rewrite (EE 3%nat 3%bv eq_refl) in Q3.
  rewrite (EE 4%nat 4%bv eq_refl) in Q4. rewrite (EE 8%nat 8%bv eq_refl) in Q8.
  rewrite (EE 9%nat 9%bv eq_refl) in Q9. rewrite (EE 18%nat 18%bv eq_refl) in Q18.
  rewrite (EE 20%nat 20%bv eq_refl) in Q20. rewrite (EE 24%nat 24%bv eq_refl) in Q24.
  rewrite F32 in Q25.
  pose proof HS as (Pfr & Ppc & Ppend & Presv & Pfcsr & Prom & Pregs & _).
  cbn [restrict ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst ss_pc abs_ss setpc]
    in Pfr, Ppc, Ppend, Presv, Prom, Pfcsr.
  pose proof HMJ as (JSV & JSH & JFL & JFR & JSR & JCUR & J68 & JIN & JREG & JPREV).
  assert (HBODY : gb_body cx fp GP_J W3 msF GSH_J).
  { unfold gb_body, gregs.
    split; [exact Ppc|]. split; [exact Presv|]. split; [exact Ppend|]. split; [exact Prom|].
    split; [exact Pfr|]. split; [exact Pfcsr|].
    split.
    { split; [rewrite Q2, G2; reflexivity|]. split; [rewrite Q8, G8; reflexivity|].
      split; [rewrite Q9, G9; reflexivity|]. split; [rewrite Q3, G3; reflexivity|].
      split; [rewrite Q4, G4; reflexivity|]. split; [rewrite Q18, G18; reflexivity|].
      rewrite Q24, G24; reflexivity. }
    split; [exact JSV|]. split; [exact JSH|].
    split; [vm_compute; reflexivity|]. split; [exact JFL|]. split; [exact JFR | exact JIN]. }
  apply (HJN ltac:(lia) cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
  unfold GI_J. exists r, bs', pos.
  split; [exact HBODY|]. split; [lia|]. split; [lia|]. split; [exact Hacc|].
  split; [exact HBLK|].
  split; [split; [exact HRIN|]; split; [exact HLEN' | exact JREG]|].
  split; [exact HINV'|].
  split; [rewrite Q20, G20; reflexivity|].
  split.
  { pose proof (st_ok_pi_restrict_reg (w_H W3) E _ msF (21%bv : bv 5) HS) as Q21.
    lazymatch type of Q21 with _ = sv_denot _ (sr_get (ss_regs ?ss) _) =>
      let e := eval vm_compute in (sr_get (ss_regs ss) (21%bv : bv 5)) in
      change (sr_get (ss_regs ss) (21%bv : bv 5)) with e in Q21 end.
    rewrite Q21, denot_lit_U, (jn_U_addiw E 33%nat i F33 ltac:(lia)). reflexivity. }
  split; [rewrite HFAB; rewrite Q25; reflexivity|].
  split; [rewrite HFAB; exact JSR | exact JCUR].
- (* i + 1 = 64: the exit at 0x80e14 *)
  rewrite branch_ne_U, (jn_U_addiw E 33%nat i F33 ltac:(lia)), U_SLit in Hc.
  change (zcanon 64) with 64 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK JBspan GP_X; [jn_awr U24 |].
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
  assert (KOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (gSH cx fp + 4 <= a < gSH cx fp + 44) ->
    aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) mem a).
  { intros a Ha Hn.
    repeat match goal with
    | HFx : frame_of ?Ex ?rsx ?m1 ?m2 |- _ =>
        let Hq := fresh "KQ" in
        assert (Hq : aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem msF) a) by reflexivity;
        clear Hq;
        first
        [ (let Hq := fresh "KQ" in
           assert (Hq : aview SEGS (w_H W3) m2 a = aview SEGS (w_H W3) m1 a)
             by (first [ apply (jn_keep_outside Ex rsx _ _ a HFx Ha)
                       | apply (jn_keep_outside_raw Ex rsx m1 m2 a HFx Ha) ];
                 intros (rg & Hin & Hb); vm_compute in Hin;
                 repeat (destruct Hin as [<- | Hin];
                   [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb;
                    try rewrite U24 in Hb; try rewrite U9 in Hb; lia |]);
                 exact Hin);
           clear HFx; try rewrite Hq; clear Hq)
        | clear HFx ]
    end; reflexivity. }
  pose proof (st_ok_pi_region_nth E _ (restrict (w_H W3) msF) 1%nat _ HS eq_refl) as Rsh.
  cbn [restrict ms_mem mkst] in Rsh.
  assert (SHJ : forall q, 0 <= q < 52 ->
    aview SEGS (w_H W3) (ms_mem msF) (gSH cx fp + q) = Some (nth (Z.to_nat q) GSH_J 0)).
  { intros q Hq. assert (Hcase : q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 11 \/ q = 12 \/ q = 13 \/ q = 14 \/ q = 15 \/ q = 16 \/ q = 17 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27 \/ q = 28 \/ q = 29 \/ q = 30 \/ q = 31 \/ q = 32 \/ q = 33 \/ q = 34 \/ q = 35 \/ q = 36 \/ q = 37 \/ q = 38 \/ q = 39 \/ q = 40 \/ q = 41 \/ q = 42 \/ q = 43 \/ q = 44 \/ q = 45 \/ q = 46 \/ q = 47 \/ q = 48 \/ q = 49 \/ q = 50 \/ q = 51) by lia.
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    destruct Hcase as [-> | Hcase];
    [ eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity] |].
    rewrite Hcase.
    eapply (jn_byte_of_region E (ms_mem msF) 24%nat (gSH cx fp));
      [exact Rsh | exact U24 | jn_in_chunk | vm_compute; reflexivity]. }
  assert (HMJ : jn_mem GSH_J (ms_mem msF)).
  { apply (jn_land_mem msF mem (ms_mem msF) _ (proj1 HJ) HM KOUT).
    intros q Hq.
    assert (Hq52 : (q < 52)%nat) by (revert Hq; vm_compute (length GSH_J); lia).
    pose proof (SHJ (Z.of_nat q) ltac:(lia)) as HSq. rewrite Nat2Z.id in HSq. exact HSq. }
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  rewrite (EE 2%nat 2%bv eq_refl) in Q2. rewrite (EE 3%nat 3%bv eq_refl) in Q3.
  rewrite (EE 4%nat 4%bv eq_refl) in Q4. rewrite (EE 8%nat 8%bv eq_refl) in Q8.
  rewrite (EE 9%nat 9%bv eq_refl) in Q9. rewrite (EE 18%nat 18%bv eq_refl) in Q18.
  rewrite (EE 20%nat 20%bv eq_refl) in Q20. rewrite (EE 24%nat 24%bv eq_refl) in Q24.
  rewrite F32 in Q25.
  pose proof HS as (Pfr & Ppc & Ppend & Presv & Pfcsr & Prom & Pregs & _).
  cbn [restrict ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst ss_pc abs_ss setpc]
    in Pfr, Ppc, Ppend, Presv, Prom, Pfcsr.
  pose proof HMJ as (JSV & JSH & JFL & JFR & JSR & JCUR & J68 & JIN & JREG & JPREV).
  assert (HBODY : gb_body cx fp GP_X W3 msF GSH_J).
  { unfold gb_body, gregs.
    split; [exact Ppc|]. split; [exact Presv|]. split; [exact Ppend|]. split; [exact Prom|].
    split; [exact Pfr|]. split; [exact Pfcsr|].
    split.
    { split; [rewrite Q2, G2; reflexivity|]. split; [rewrite Q8, G8; reflexivity|].
      split; [rewrite Q9, G9; reflexivity|]. split; [rewrite Q3, G3; reflexivity|].
      split; [rewrite Q4, G4; reflexivity|]. split; [rewrite Q18, G18; reflexivity|].
      rewrite Q24, G24; reflexivity. }
    split; [exact JSV|]. split; [exact JSH|].
    split; [vm_compute; reflexivity|]. split; [exact JFL|]. split; [exact JFR | exact JIN]. }
  apply (HXN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO).
  unfold GI_X. exists r.
  split; [exact HBODY|]. split; [lia|].
  split; [replace 64 with (i + 1) by lia; exact Hacc|].
  split; [exact HBLK|]. split; [exact HRIN|].
  rewrite Q20, G20; reflexivity.
Qed.

(* ---- one turn of the inlined check_kept, row j ---- *)
Definition jn_R_slots_loop : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 152 0 0 [YP09.mkChunk 0x78 (CVal 8 (SOff 32%nat 0))].
Definition jn_R_row (base : nat) (j : Z) : YP09.region :=
  YP09.mkRegion (Some base) 0 288 0 0
    [YP09.mkChunk (56 * j + 8) (CVal 4 (SOff 35%nat 0));
     YP09.mkChunk (56 * j + 12) (CVal 4 (SOff 36%nat 0));
     YP09.mkChunk (56 * j + 20) (CVal 4 (SOff 37%nat 0))].
Definition jn_R_rsh : YP09.region := YP09.mkRegion (Some 34%nat) 0 36 0 0 [YP09.mkChunk 0 (CZero 36)].
Definition jn_R_psh : YP09.region := YP09.mkRegion (Some 33%nat) 0 36 0 0 [YP09.mkChunk 0 (CZero 36)].
Definition jn_AF_loop : list (nat * afact) :=
  [(20%nat, mkAF 4096 (2 ^ 47) 4); (32%nat, mkAF 4096 (2 ^ 47) 3);
   (35%nat, mkAF 0 38 0); (36%nat, mkAF 2 40 0); (37%nat, mkAF 0 1 0)].
Definition jn_AL_loop : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 20%nat 0) (SLit 3)) (SOff 18%nat 0), SOff 34%nat 0);
   (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32%nat 0) (SLit 3)) (SOff 18%nat 0), SOff 33%nat 0)].
Definition jn_sr_loop (j : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (22%bv : bv 5) (SLit (56 * j)))
    (25%bv : bv 5) (SOff 38%nat 0)) (27%bv : bv 5) (SOff 39%nat 0))
    (26%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20%nat (8 + 56 * j)) (SLit 3)) (SOff 18%nat 0)).
Definition jn_ss_loop (j : Z) : sstate :=
  mkSS JP_head (jn_sr_loop j) [jn_R_slots_loop; jn_R_row 20 j; jn_R_row 32 j; jn_R_rsh; jn_R_psh]
    None (mkFacts jn_AF_loop [] jn_AL_loop).
Definition jn_ex (j : Z) : list word :=
  [w64 (gF cx fp + GO_PREV); w64 (shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV));
   w64 (shadow_of_addr SHADOW_OFF r); w64 (jn_u bs (56 * j + 8)); w64 (jn_u bs (56 * j + 12));
   w64 (jn_u bs (56 * j + 20)); w64 (56 * Boxreg.bx_n bs); w64 (56 * (ren mod 2 ^ 32))].

(* What a turn carries at the head of the loop. *)
Definition JINV (j : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  0 <= j < Boxreg.bx_n bs /\
  getr regs 2 = w64 (c_sp1 cx) /\ getr regs 8 = w64 (spZ (c_regs cx)) /\ getr regs 9 = w64 (c_sp1 cx) /\
  getr regs 3 = getr (c_regs cx) 3 /\ getr regs 4 = getr (c_regs cx) 4 /\
  getr regs 18 = w64 SHADOW_OFF /\ getr regs 24 = w64 (gSH cx fp) /\ getr regs 20 = w64 r /\
  getr regs 22 = w64 (56 * j) /\ getr regs 25 = w64 (56 * Boxreg.bx_n bs) /\
  getr regs 26 = w64 (shadow_of_addr SHADOW_OFF (r + 8 + 56 * j)) /\
  getr regs 27 = w64 (56 * (ren mod 2 ^ 32)) /\
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 mem md k /\
  jn_mem GSH_it mem.

(* The registers of the cut that a call of the string runtime keeps. *)
Lemma jn_pres : forall (regs regs' : bvmap 5 word) (q : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned q) -> getr regs' q = getr regs q.
Proof.
intros regs regs' q HP Hq. pose proof (HP (bv_unsigned q) Hq) as H.
rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* The five extents of a turn's seat are pairwise apart: the registry block, the frame's `prev`, their two shadow
   ranges and the spill slots. *)
Lemma jn_disj : forall (m : word -> option byte) md2, AR SEGS B ly3 S3 W3 m md2 ->
  (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r) /\
  (shadow_of_addr SHADOW_OFF r + 36 <= shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV) \/
   shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV) + 36 <= shadow_of_addr SHADOW_OFF r).
Proof.
intros m md2 HAR.
pose proof (jn_F m md2 HAR) as (HF0 & HFc & HFia & H32 & HSHeq & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ r REG_SIZE GB_CID fp HAR HRIN jn_fin) as DSF.
rewrite jn_frame_addr in DSF. unfold zdisjoint in DSF. cbn [fst snd] in DSF.
change (req_size REG_SIZE) with 288 in DSF. change (fs_frame_bytes GB_CID) with 512 in *.
assert (Hg8 : gF cx fp mod 8 = 0).
{ apply Z.mod_divide in H32; [|lia]. apply Z.mod_divide; [lia|].
  destruct H32 as [q Hq]. exists (4 * q). lia. }
assert (Hr8 : r mod 8 = 0).
{ apply Z.mod_divide in Hr16; [|lia]. apply Z.mod_divide; [lia|].
  destruct Hr16 as [q Hq]. exists (2 * q). lia. }
split; [exact DSF|].
unfold shadow_of_addr, GO_PREV.
pose proof (Z.div_mod r 8 ltac:(lia)) as Dr. pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)) as Dg.
destruct DSF as [D | D].
- left.
  assert (Ha : (gF cx fp + 64) / 8 = gF cx fp / 8 + 8)
    by (rewrite (Z.div_mod (gF cx fp) 8) at 1 by lia; rewrite Hg8, Z.add_0_r;
        replace (8 * (gF cx fp / 8) + 64) with ((gF cx fp / 8 + 8) * 8) by lia;
        rewrite Z.div_mul by lia; reflexivity).
  assert (Hb : r / 8 + 36 <= gF cx fp / 8 + 8).
  { assert (Hle : r / 8 + 36 <= (gF cx fp) / 8 + 8) by
      (pose proof (Z.div_le_mono (r + 288) (gF cx fp) 8 ltac:(lia) D) as Hm;
       rewrite (Z.div_mod r 8) in Hm by lia; rewrite Hr8, Z.add_0_r in Hm;
       replace (8 * (r / 8) + 288) with ((r / 8 + 36) * 8) in Hm by lia;
       rewrite Z.div_mul in Hm by lia; lia).
    exact Hle. }
  rewrite Ha. lia.
- right.
  assert (Ha : (gF cx fp + 64) / 8 = gF cx fp / 8 + 8)
    by (rewrite (Z.div_mod (gF cx fp) 8) at 1 by lia; rewrite Hg8, Z.add_0_r;
        replace (8 * (gF cx fp / 8) + 64) with ((gF cx fp / 8 + 8) * 8) by lia;
        rewrite Z.div_mul by lia; reflexivity).
  assert (Hb : gF cx fp / 8 + 64 <= r / 8).
  { pose proof (Z.div_le_mono (gF cx fp + 512) r 8 ltac:(lia) D) as Hm.
    rewrite (Z.div_mod (gF cx fp) 8) in Hm by lia. rewrite Hg8, Z.add_0_r in Hm.
    replace (8 * (gF cx fp / 8) + 512) with ((gF cx fp / 8 + 64) * 8) in Hm by lia.
    rewrite Z.div_mul in Hm by lia. lia. }
  rewrite Ha. lia.
Qed.

(* The three fields of a row, as the numbers the machine compares. *)
Lemma jn_fields : forall jj, 0 <= jj < Boxreg.bx_n bs ->
  jn_u bs (56 * jj + 8) = Boxreg.bx_base bs jj /\ 0 <= Boxreg.bx_base bs jj <= 38 /\
  jn_u bs (56 * jj + 12) = Boxreg.bx_nch bs jj /\ 2 <= Boxreg.bx_nch bs jj <= 40 /\
  jn_u bs (56 * jj + 20) = Boxreg.bx_pinned bs jj /\ 0 <= Boxreg.bx_pinned bs jj <= 1.
Proof.
intros jj Hjj. pose proof (jn_n_small bs HINV) as Hn5.
pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hren32.
pose proof HINV as ((_ & HB1 & HB2 & HB3 & _) & HB7).
destruct (HB3 jj Hjj) as (_ & Hw1 & Hw2 & Hb1 & Hb2). destruct (HB7 jj Hjj) as (Hp & _).
unfold Boxreg.boxreg_B2 in HB2.
assert (Hbase : jn_u bs (56 * jj + 8) = Boxreg.bx_base bs jj)
  by (unfold Boxreg.bx_base; apply jn_u_of_rd4; [lia | rewrite HLEN; lia | unfold Boxreg.bx_base in Hb1; lia]).
assert (Hnch : jn_u bs (56 * jj + 12) = Boxreg.bx_nch bs jj)
  by (unfold Boxreg.bx_nch; apply jn_u_of_rd4; [lia | rewrite HLEN; lia | unfold Boxreg.bx_nch in Hw1; lia]).
assert (Hpin : jn_u bs (56 * jj + 20) = Boxreg.bx_pinned bs jj)
  by (unfold Boxreg.bx_pinned; apply jn_u_of_rd4; [lia | rewrite HLEN; lia | unfold Boxreg.bx_pinned in Hp; lia]).
split; [exact Hbase|]. split; [lia|]. split; [exact Hnch|]. split; [lia|]. split; [exact Hpin | lia].
Qed.

(* The shadow of the registry block and of `prev`, as the seat's two CZero regions. *)
Lemma jn_rsh_zero : forall (m : word -> option byte) md2 q, AR SEGS B ly3 S3 W3 m md2 -> 0 <= q < 36 ->
  aview SEGS (w_H W3) m (shadow_of_addr SHADOW_OFF r + q) = Some 0.
Proof.
intros m md2 q Hq HAR.
destruct (al_shadow _ _ LAWS _ _ _ _ _ r REG_SIZE Hq HRIN) as (HBS & _).
change (req_size REG_SIZE) with 288 in HBS.
destruct HBS as (Hp8 & Hn0 & Hc). pose proof (Hc q ltac:(change ((288 + 7) / 8) with 36; lia)) as Hq8.
replace (if q <? 288 / 8 then 0 else 288 mod 8) with 0 in Hq8
  by (change (288 / 8) with 36; destruct (Z.ltb_spec q 36); [reflexivity | lia]).
exact Hq8.
Qed.

Lemma jn_psh_zero : forall (m : word -> option byte) md2 q, AR SEGS B ly3 S3 W3 m md2 ->
  gshadow cx fp W3 (jms m) GSH_it -> 0 <= q < 36 ->
  aview SEGS (w_H W3) m (shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV) + q) = Some 0.
Proof.
intros m md2 q HAR HSH Hq.
pose proof (jn_F m md2 HAR) as (_ & _ & _ & H32 & _).
assert (Hg8 : gF cx fp mod 8 = 0).
{ apply Z.mod_divide in H32; [|lia]. apply Z.mod_divide; [lia|].
  destruct H32 as [qq Hqq]. exists (4 * qq). lia. }
assert (E1 : shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV) + q
           = shadow_of_addr SHADOW_OFF (gF cx fp + (GO_PREV + 8 * q))).
{ rewrite (shadow_of_addr_aligned_off SHADOW_OFF (gF cx fp) GO_PREV Hg8).
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (gF cx fp) (GO_PREV + 8 * q) Hg8).
  unfold GO_PREV. replace (64 + 8 * q) with (q * 8 + 64) by lia.
  rewrite Z.div_add_l by lia. change (64 / 8) with 8. lia. }
rewrite E1. apply (jn_frame_sh0 m md2 (GO_PREV + 8 * q) HAR HSH). unfold GO_PREV. lia.
Qed.

(* The seat of a turn: the cut's facts as the engine's symbolic state at the loop head. *)
Lemma jn_seat : forall j (regs : bvmap 5 word) mem md,
  0 <= j < Boxreg.bx_n bs ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 9 = w64 (c_sp1 cx) -> getr regs 18 = w64 SHADOW_OFF ->
  getr regs 20 = w64 r -> getr regs 22 = w64 (56 * j) -> getr regs 25 = w64 (56 * Boxreg.bx_n bs) ->
  getr regs 26 = w64 (shadow_of_addr SHADOW_OFF (r + 8 + 56 * j)) ->
  getr regs 27 = w64 (56 * (ren mod 2 ^ 32)) ->
  AR SEGS B ly3 S3 W3 mem md -> jn_mem GSH_it mem ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (jn_ex j))) (jn_ss_loop j)
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + JP_head)) mem (seg_rom SEGS))).
Proof.
intros j regs mem md Hj G2 G9 G18 G20 G22 G25 G26 G27 HAR HM.
pose proof (jn_n_small bs HINV) as Hn5.
pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hren32.
pose proof jn_sp as (Hal16 & Hceil & H47 & Hsp1 & Hsp32). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & _).
pose proof (jn_F mem md HAR) as (HF0 & HFc & HFia & HF32 & HSHeq & HSHp & HFp).
pose proof (jn_sh_range mem md HAR) as (HS0 & HS1 & HSdF & HSdsp).
change (fs_frame_bytes GB_CID) with 512 in HF0, HFc, HFia, HSHp, HFp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
destruct (jn_disj mem md HAR) as (DRF & DSH).
destruct (jn_fields j Hj) as (Eu8 & Hb38 & Eu12 & Hn40 & Eu20 & Hp1).
destruct (jn_row_u bs bs' ren j HLEN HLEN' HINV HKEPT Hj) as (Rb & Rn & Rp).
pose proof HM as (_ & MSH & _ & (_ & _ & _ & MF78 & _) & _ & _ & _ & _ & MREG & MPREV).
assert (Hg8 : gF cx fp mod 8 = 0).
{ apply Z.mod_divide in HF32; [|lia]. apply Z.mod_divide; [lia|].
  destruct HF32 as [q Hq]. exists (4 * q). lia. }
set (E := Eimg (Ereg regs (jn_ex j))).
assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
  by (intros q rr Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (EX : forall q, (q < 8)%nat -> ew E (32 + q)%nat = nth q (jn_ex j) (Z_to_bv 64 0))
  by (intros q Hq; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (F32 : ew E 32 = w64 (gF cx fp + GO_PREV)) by (exact (EX 0%nat ltac:(lia))).
assert (F33 : ew E 33 = w64 (shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV))) by (exact (EX 1%nat ltac:(lia))).
assert (F34 : ew E 34 = w64 (shadow_of_addr SHADOW_OFF r)) by (exact (EX 2%nat ltac:(lia))).
assert (F35 : ew E 35 = w64 (jn_u bs (56 * j + 8))) by (exact (EX 3%nat ltac:(lia))).
assert (F36 : ew E 36 = w64 (jn_u bs (56 * j + 12))) by (exact (EX 4%nat ltac:(lia))).
assert (F37 : ew E 37 = w64 (jn_u bs (56 * j + 20))) by (exact (EX 5%nat ltac:(lia))).
assert (F38 : ew E 38 = w64 (56 * Boxreg.bx_n bs)) by (exact (EX 6%nat ltac:(lia))).
assert (F39 : ew E 39 = w64 (56 * (ren mod 2 ^ 32))) by (exact (EX 7%nat ltac:(lia))).
assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
assert (F20 : ew E 20 = w64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact G20).
assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = r) by (rewrite F20; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = gF cx fp + GO_PREV)
  by (rewrite F32; apply unsigned_lit_small; unfold GO_PREV; lia).
assert (Hsr : 0 <= shadow_of_addr SHADOW_OFF r /\ shadow_of_addr SHADOW_OFF r + 36 <= 2 ^ 64).
{ unfold shadow_of_addr, SHADOW_OFF.
  pose proof (Z.div_pos r 8 ltac:(lia) ltac:(lia)) as Dp.
  pose proof (Z.mul_div_le r 8 ltac:(lia)) as Dm. lia. }
assert (Hsp : 0 <= shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV) /\
               shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV) + 36 <= 2 ^ 64).
{ unfold shadow_of_addr, SHADOW_OFF, GO_PREV.
  pose proof (Z.div_pos (gF cx fp + 64) 8 ltac:(lia) ltac:(lia)) as Dp2.
  pose proof (Z.mul_div_le (gF cx fp + 64) 8 ltac:(lia)) as Dm2. lia. }
assert (U33 : bv_unsigned (ew E 33) = shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV))
  by (rewrite F33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = shadow_of_addr SHADOW_OFF r)
  by (rewrite F34; apply unsigned_lit_small; lia).
assert (HSB0 : 0 <= SHADOW_OFF) by (unfold SHADOW_OFF; lia).
assert (HSB1 : SHADOW_OFF + (r + (8 + 56 * j)) / 8 < 2 ^ 64).
{ pose proof (Z.mul_div_le (r + (8 + 56 * j)) 8 ltac:(lia)) as M1.
  pose proof (Z.div_pos (r + (8 + 56 * j)) 8 ltac:(lia) ltac:(lia)) as M2.
  unfold SHADOW_OFF. lia. }
assert (HSB2 : SHADOW_OFF + (r + 0) / 8 < 2 ^ 64).
{ pose proof (Z.mul_div_le (r + 0) 8 ltac:(lia)) as M1.
  pose proof (Z.div_pos (r + 0) 8 ltac:(lia) ltac:(lia)) as M2.
  unfold SHADOW_OFF. lia. }
assert (HSB3 : SHADOW_OFF + (gF cx fp + GO_PREV + 0) / 8 < 2 ^ 64).
{ pose proof (Z.mul_div_le (gF cx fp + GO_PREV + 0) 8 ltac:(unfold GO_PREV; lia)) as M1.
  pose proof (Z.div_pos (gF cx fp + GO_PREV + 0) 8 ltac:(unfold GO_PREV; lia) ltac:(lia)) as M2.
  unfold SHADOW_OFF, GO_PREV in *. lia. }
rewrite restrict_mkst_fx. unfold jn_ss_loop. apply pa_entry_st_ok_full.
- (* the registers of the seat *)
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
    [unfold E; apply regs_ok_Eimg_Ereg | discriminate | ] | discriminate | ] | discriminate | ] | discriminate | ].
  + rewrite G22. cbn [sv_denot]. reflexivity.
  + rewrite G25. cbn [sv_denot]. rewrite F38, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + rewrite G27. cbn [sv_denot]. rewrite F39, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + rewrite G26. symmetry.
    rewrite (jn_U_shadow E 20%nat r (8 + 56 * j) SHADOW_OFF F20 F18 ltac:(lia) ltac:(lia) ltac:(lia)
      HSB0 HSB1).
    unfold shadow_of_addr. f_equal. f_equal. f_equal. lia.
- (* the regions are well formed *)
  unfold jn_R_slots_loop, jn_R_row, jn_R_rsh, jn_R_psh, YP09.regions_wf, YP09.region_wf, YP09.chunk_inside.
  cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.c_off YP09.c_len YP09.c_val
       cv_len forallb andb orb].
  repeat (apply andb_true_intro; split); try reflexivity; try (apply Z.leb_le; lia); try (apply orb_true_intro; left; reflexivity).
- (* every region holds what the cut says *)
  apply Forall_cons;
  [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
  + unfold jn_R_slots_loop, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) (c_sp1 cx) 0x78 8%N (SOff 32%nat 0)
             (gF cx fp + GO_PREV)).
    * cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold GO_PREV. lia.
    * change (Z.of_N 8) with 8. lia.
    * apply (val_mem_of_rdword SEGS (w_H W3) mem). exact MF78.
  + unfold jn_R_row, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) r (56 * j + 8) 4%N (SOff 35%nat 0)
               (jn_u bs' (56 * j + 8))).
      -- cbn [sv_denot]. rewrite F35, Rb, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). pose proof (jn_u_range bs' (56 * j + 8)). lia.
      -- change (Z.of_N 4) with 4. lia.
      -- apply (jn_val4 mem r bs' (56 * j + 8) MREG); unfold REG_SIZE; lia.
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) r (56 * j + 12) 4%N (SOff 36%nat 0)
               (jn_u bs' (56 * j + 12))).
      -- cbn [sv_denot]. rewrite F36, Rn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). pose proof (jn_u_range bs' (56 * j + 12)). lia.
      -- change (Z.of_N 4) with 4. lia.
      -- apply (jn_val4 mem r bs' (56 * j + 12) MREG); unfold REG_SIZE; lia.
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) r (56 * j + 20) 4%N (SOff 37%nat 0)
               (jn_u bs' (56 * j + 20))).
      -- cbn [sv_denot]. rewrite F37, Rp, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). pose proof (jn_u_range bs' (56 * j + 20)). lia.
      -- change (Z.of_N 4) with 4. lia.
      -- apply (jn_val4 mem r bs' (56 * j + 20) MREG); unfold REG_SIZE; lia.
  + unfold jn_R_row, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U32. split; [unfold GO_PREV; lia|]. split; [unfold GO_PREV; lia|]. split; [intros o Ho; lia|].
    assert (MPB : forall q, 0 <= q < REG_SIZE ->
      aview SEGS (w_H W3) mem (gF cx fp + GO_PREV + q) = Some (jn_b bs q)) by exact MPREV.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) (gF cx fp + GO_PREV) (56 * j + 8) 4%N
               (SOff 35%nat 0) (jn_u bs (56 * j + 8))).
      -- cbn [sv_denot]. rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). pose proof (jn_u_range bs (56 * j + 8)). lia.
      -- change (Z.of_N 4) with 4. lia.
      -- apply (jn_val4 mem (gF cx fp + GO_PREV) bs (56 * j + 8) MPB); unfold REG_SIZE; lia.
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) (gF cx fp + GO_PREV) (56 * j + 12) 4%N
               (SOff 36%nat 0) (jn_u bs (56 * j + 12))).
      -- cbn [sv_denot]. rewrite F36, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). pose proof (jn_u_range bs (56 * j + 12)). lia.
      -- change (Z.of_N 4) with 4. lia.
      -- apply (jn_val4 mem (gF cx fp + GO_PREV) bs (56 * j + 12) MPB); unfold REG_SIZE; lia.
    * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) (gF cx fp + GO_PREV) (56 * j + 20) 4%N
               (SOff 37%nat 0) (jn_u bs (56 * j + 20))).
      -- cbn [sv_denot]. rewrite F37, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). pose proof (jn_u_range bs (56 * j + 20)). lia.
      -- change (Z.of_N 4) with 4. lia.
      -- apply (jn_val4 mem (gF cx fp + GO_PREV) bs (56 * j + 20) MPB); unfold REG_SIZE; lia.
  + unfold jn_R_rsh, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    intros q Hq. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len cbyte] in *.
    exists (Z_to_bv 8 0). split; [reflexivity|].
    rewrite Z.add_0_r.
    destruct (aview_byte SEGS (w_H W3) mem (shadow_of_addr SHADOW_OFF r + q) 0
      (jn_rsh_zero mem md q HAR ltac:(lia))) as (b & Hb & Hv & _).
    rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with 256. rewrite <- Hv. reflexivity.
  + unfold jn_R_psh, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    intros q Hq. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len cbyte] in *.
    exists (Z_to_bv 8 0). split; [reflexivity|].
    rewrite Z.add_0_r.
    destruct (aview_byte SEGS (w_H W3) mem (shadow_of_addr SHADOW_OFF (gF cx fp + GO_PREV) + q) 0
      (jn_psh_zero mem md q HAR MSH ltac:(lia))) as (b & Hb & Hv & _).
    rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with 256. rewrite <- Hv. reflexivity.
- (* the five extents are pairwise apart *)
  apply pairwise_disjoint_of_extents.
  unfold jn_R_slots_loop, jn_R_row, jn_R_rsh, jn_R_psh, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite U9, U20, U32, U33, U34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg in HFia, Hria.
  unfold shadow_of_addr, GO_PREV, SHADOW_OFF in *.
  pose proof (Z.div_pos r 8 ltac:(lia) ltac:(lia)) as P1.
  pose proof (Z.div_pos (gF cx fp + 64) 8 ltac:(lia) ltac:(lia)) as P2.
  pose proof (Z.mul_div_le r 8 ltac:(lia)) as P3.
  pose proof (Z.mul_div_le (gF cx fp + 64) 8 ltac:(lia)) as P4.
  repeat split; lia.
- (* the atom facts and the two shadow aliases *)
  split.
  { cbn [jn_AF_loop f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U32, F35, F36, F37.
    rewrite !unsigned_lit_small by (pose proof (jn_u_range bs (56 * j + 8));
      pose proof (jn_u_range bs (56 * j + 12)); pose proof (jn_u_range bs (56 * j + 20)); lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold ASAN_CEIL, GO_PREV in *. change (fs_frame_bytes GB_CID) with 512 in *.
    assert (A8 : (gF cx fp + 64) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hg8; reflexivity).
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia; first [exact Hr16 | exact A8]. }
  split; [exact I|].
  cbn [jn_AL_loop f_alias alias_ok]. split; [|split; [|exact I]].
  + rewrite (jn_U_shadow E 20%nat r 0 SHADOW_OFF F20 F18 ltac:(lia) ltac:(lia) ltac:(lia) HSB0 HSB2).
    rewrite (denot_lit_U E (SOff 34%nat 0)), U_SOff, F34.
    rewrite unsigned_lit_small by lia. rewrite !Z.add_0_r.
    rewrite zcanon_id by (unfold M64; lia). reflexivity.
  + rewrite (jn_U_shadow E 32%nat (gF cx fp + GO_PREV) 0 SHADOW_OFF F32 F18 ltac:(unfold GO_PREV; lia)
      ltac:(lia) ltac:(unfold GO_PREV; lia) HSB0 HSB3).
    rewrite (denot_lit_U E (SOff 33%nat 0)), U_SOff, F33.
    rewrite unsigned_lit_small by lia. rewrite !Z.add_0_r.
    rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

Lemma jn_at_range : forall (m : word -> option byte) md2, AR SEGS B ly3 S3 W3 m md2 ->
  forall a, jn_at a -> 0 <= a < 2 ^ 64.
Proof.
intros m md2 HAR a Ha.
pose proof jn_sp as (_ & Hceil & H47 & Hsp1 & _). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & _).
pose proof (jn_F m md2 HAR) as (HF0 & HFc & _ & _ & HSHeq & _).
pose proof (jn_sh_range m md2 HAR) as (HSL0 & HSL1 & _ & _).
change (fs_frame_bytes GB_CID) with 512 in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (_ & Hr4096 & Hrceil & _ & _).
change (req_size REG_SIZE) with 288 in Hrceil.
pose proof HB as (_ & _ & _ & Hpn & _).
assert (Hp : 0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling \/ c_n cx = 0).
{ destruct Hpn as [[Hn0 _] | [Hn Hin]]; [right; lia|].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & _ & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. left. lia. }
unfold jn_at, REG_SIZE in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
- lia.
- lia.
- lia.
- lia.
- lia.
Qed.

(* A segment of the walk whose regions are all read-only keeps every byte the cut speaks about. *)
Lemma jn_mem_ro : forall (E' : env) rs (m m' m0 : word -> option byte) md2,
  AR SEGS B ly3 S3 W3 m0 md2 ->
  frame_of E' rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  (forall rg, In rg rs -> YP09.r_whi rg <= YP09.r_wlo rg) ->
  jn_mem GSH_it m -> jn_mem GSH_it m'.
Proof.
intros E' rs m m' m0 md2 HAR HF Hro HM.
apply (jn_mem_keep GSH_it m m' HM); [|vm_compute; lia].
intros a Ha. apply (jn_keep_outside E' rs m m' a HF (jn_at_range m0 md2 HAR a Ha)).
intros (rg & Hin & Hb). pose proof (Hro rg Hin). lia.
Qed.

Lemma jn_mem_ro_raw : forall (E' : env) rs (m m' m0 : word -> option byte) md2,
  AR SEGS B ly3 S3 W3 m0 md2 -> frame_of E' rs m m' ->
  (forall rg, In rg rs -> YP09.r_whi rg <= YP09.r_wlo rg) ->
  jn_mem GSH_it m -> jn_mem GSH_it m'.
Proof.
intros E' rs m m' m0 md2 HAR HF Hro HM.
apply (jn_mem_keep GSH_it m m' HM); [|vm_compute; lia].
intros a Ha. apply (jn_keep_outside_raw E' rs m m' a HF (jn_at_range m0 md2 HAR a Ha)).
intros (rg & Hin & Hb). pose proof (Hro rg Hin). lia.
Qed.

Ltac jn_ro_regions :=
  intros rg Hin; vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi]; lia |]); exfalso; exact Hin.

(* Carry the cut's memory facts across an engine segment that wrote nothing: find the segment's frame hypothesis
   from the memory of HMx to the memory of the goal. *)
Ltac jn_carry HARx HMx HMy :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?ms; cfg_model := _ |} _ =>
    lazymatch type of HMx with jn_mem GSH_it ?m0 =>
      first [ match goal with Hf : frame_of _ _ m0 (ms_mem ms) |- _ =>
                assert (HMy : jn_mem GSH_it (ms_mem ms))
                  by (eapply (jn_mem_ro_raw _ _ _ _ _ _ HARx Hf ltac:(jn_ro_regions) HMx)) end
            | match goal with Hf : frame_of _ _ (mrestrict _ m0) (mrestrict _ (ms_mem ms)) |- _ =>
                assert (HMy : jn_mem GSH_it (ms_mem ms))
                  by (eapply (jn_mem_ro _ _ _ _ _ _ HARx Hf ltac:(jn_ro_regions) HMx)) end ]
    end
  end.

Lemma jn_denot_off : forall (E' : env) (n : nat) (v c : Z),
  bv_unsigned (ew E' n) = v -> 0 <= v + c < 2 ^ 64 -> sv_denot E' (SOff n c) = w64 (v + c).
Proof.
intros E' n v c Hv Hc. rewrite denot_lit_U, U_SOff, Hv, zcanon_id by (unfold M64; lia). reflexivity.
Qed.

Lemma jn_shadow_eq : forall a b, a = b -> w64 (SHADOW_OFF + a / 8) = w64 (shadow_of_addr SHADOW_OFF b).
Proof. intros a b ->. unfold shadow_of_addr. reflexivity. Qed.

Lemma jn_denot_atom : forall (E' : env) (n : nat), sv_denot E' (SOff n 0) = ew E' n.
Proof.
intros E' n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E' n)) as HR. change (bv_modulus 64) with M64 in HR.
rewrite zcanon_id by exact HR. apply Z_to_bv_bv_unsigned.
Qed.

Lemma jn_denot_lit : forall (E' : env) (z : Z), 0 <= z < 2 ^ 64 -> sv_denot E' (SLit z) = w64 z.
Proof.
intros E' z Hz. rewrite denot_lit_U, U_SLit, zcanon_id by (unfold M64; lia). reflexivity.
Qed.

(* Read one register off the engine's state at a stop. *)
Ltac jn_rv HSx rr Q :=
  first [ pose proof (st_ok_reg _ _ _ _ rr HSx) as Q
        | pose proof (st_ok_pi_restrict_reg (w_H W3) _ _ _ rr HSx) as Q ];
  try (cbn [restrict ms_regs mkst] in Q);
  try (lazymatch type of Q with _ = sv_denot _ (sr_get (ss_regs ?ss) _) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) rr) in
    change (sr_get (ss_regs ss) rr) with e in Q
  end).

(* What a call of the string runtime keeps: every byte the cut speaks about lies outside its window. *)
Lemma jn_mem_call : forall (m m' m0 : word -> option byte) md2 (spv : Z),
  AR SEGS B ly3 S3 W3 m0 md2 -> spv = c_sp1 cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spv - 2 * ESTACK <= a < spv) ->
     aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  jn_mem GSH_it m -> jn_mem GSH_it m'.
Proof.
intros m m' m0 md2 spv HAR Hspv HK HM.
apply (jn_mem_keep GSH_it m m' HM); [|vm_compute; lia].
intros a Ha. pose proof (jn_at_range m0 md2 HAR a Ha) as Hr. apply HK; [exact Hr|].
pose proof jn_sp as (_ & Hceil & H47 & Hsp1 & _). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & _).
pose proof (jn_F m0 md2 HAR) as (HF0 & HFc & _ & _ & HSHeq & _).
pose proof (jn_sh_range m0 md2 HAR) as (HSL0 & HSL1 & _ & _).
change (fs_frame_bytes GB_CID) with 512 in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (_ & Hr4096 & Hrceil & _ & _).
change (req_size REG_SIZE) with 288 in Hrceil.
pose proof HB as (_ & _ & _ & Hpn & _).
assert (Hp : c_p cx + c_n cx <= alloc_ceiling \/ c_n cx = 0).
{ destruct Hpn as [[Hn0 _] | [Hn Hin]]; [right; lia|].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & _ & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. left. lia. }
assert (Hgsh : gSH cx fp + 64 <= alloc_ceiling).
{ rewrite HSHeq. unfold SHADOW_OFF.
  pose proof (Z.mul_div_le (gF cx fp) 8 ltac:(lia)). lia. }
subst spv. unfold ESTACK. unfold jn_at, REG_SIZE in Ha. lia.
Qed.

Lemma jn_cstr_prev : forall (m : word -> option byte) md2 j, AR SEGS B ly3 S3 W3 m md2 -> jn_mem GSH_it m ->
  0 <= j < Boxreg.bx_n bs -> fm_cstr_ok SEGS W3 m (gF cx fp + GO_PREV + 56 * j + 24) (jn_name bs j).
Proof.
intros m md2 j HAR HM Hj.
pose proof (jn_n_small bs HINV) as Hn5.
pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hren32.
pose proof (jn_name_len bs j HLEN ltac:(lia) HINV Hj) as Hl.
pose proof (jn_F m md2 HAR) as (HF0 & HFc & HFia & HF32 & _ & _ & _).
pose proof asan_consts as (Hac & _).
pose proof HM as (_ & MSH & _ & _ & _ & _ & _ & _ & _ & MPREV).
unfold gprev, jms in MPREV. cbn [ms_mem mkst] in MPREV.
change (fs_frame_bytes GB_CID) with 512 in *.
assert (HSUB : in_app (gF cx fp + GO_PREV + 56 * j + 24) (Z.of_nat (length (jn_name bs j)) + 8))
  by (apply (in_app_sub (gF cx fp) 512); [exact HFia | unfold GO_PREV; lia | lia | unfold GO_PREV; lia]).
destruct (jn_app_range _ _ HSUB ltac:(lia)) as (HB1 & HB2 & HB3).
unfold fm_cstr_ok, fm_cstr.
split; [split|].
- intros kk Hkk. rewrite length_app in Hkk. cbn [length] in Hkk.
  rewrite (jn_name_bytes bs j kk HLEN ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [|apply jn_b_range].
  apply jn_val_mem1.
  replace (gF cx fp + GO_PREV + 56 * j + 24 + Z.of_nat kk) with (gF cx fp + GO_PREV + (56 * j + 24 + Z.of_nat kk)) by lia.
  apply MPREV. unfold REG_SIZE. lia.
- apply jn_name_nonzero.
- split; [unfold GO_PREV; lia|]. split; [lia|].
  split; [lia|]. split; [exact HB3|].
  split; [apply (jn_frame_ra m md2 _ _ HAR MSH); unfold GO_PREV; lia|].
  split; [apply (jn_frame_hull m md2 _ _ HAR); unfold GO_PREV; lia|].
  intros a Ha.
  pose proof (Z.mod_pos_bound (gF cx fp + GO_PREV + 56 * j + 24 + Z.of_nat (length (jn_name bs j))) 8 ltac:(lia)).
  replace a with (gF cx fp + GO_PREV + (a - gF cx fp - GO_PREV)) by lia.
  rewrite (MPREV (a - gF cx fp - GO_PREV) ltac:(unfold GO_PREV, REG_SIZE in *; lia)). discriminate.
Qed.

Lemma jn_cstr_reg : forall (m : word -> option byte) md2 j, AR SEGS B ly3 S3 W3 m md2 -> jn_mem GSH_it m ->
  0 <= j < Boxreg.bx_n bs -> jn_name bs' j = jn_name bs j ->
  fm_cstr_ok SEGS W3 m (r + 56 * j + 24) (jn_name bs j).
Proof.
intros m md2 j HAR HM Hj Hnm.
pose proof (jn_n_small bs HINV) as Hn5.
pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hren32.
pose proof (jn_name_len bs j HLEN ltac:(lia) HINV Hj) as Hl.
pose proof asan_consts as (Hac & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & MREG & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (_ & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
assert (HSUB : in_app (r + 56 * j + 24) (Z.of_nat (length (jn_name bs j)) + 8))
  by (apply (in_app_sub r 288); [exact Hria | lia | lia | lia]).
destruct (jn_app_range _ _ HSUB ltac:(lia)) as (HB1 & HB2 & HB3).
destruct (jn_blk_sh m md2 (r + 56 * j + 24) (Z.of_nat (length (jn_name bs j)) + 1) HAR
  ltac:(lia) ltac:(unfold REG_SIZE; lia) ltac:(lia)) as (HRA & HHV).
unfold fm_cstr_ok, fm_cstr.
split; [split|].
- intros kk Hkk. rewrite length_app in Hkk. cbn [length] in Hkk.
  rewrite <- Hnm.
  rewrite (jn_name_bytes bs' j kk HLEN' ltac:(lia) ltac:(rewrite Hnm; lia) ltac:(lia)).
  split; [|apply jn_b_range].
  apply jn_val_mem1.
  replace (r + 56 * j + 24 + Z.of_nat kk) with (r + (56 * j + 24 + Z.of_nat kk)) by lia.
  apply MREG. unfold REG_SIZE. lia.
- apply jn_name_nonzero.
- split; [lia|]. split; [lia|].
  split; [lia|]. split; [exact HB3|].
  split; [exact HRA|]. split; [exact HHV|].
  intros a Ha.
  pose proof (Z.mod_pos_bound (r + 56 * j + 24 + Z.of_nat (length (jn_name bs j))) 8 ltac:(lia)).
  replace a with (r + (a - r)) by lia.
  rewrite (MREG (a - r) ltac:(unfold REG_SIZE in *; lia)). discriminate.
Qed.

(* The first bcmp's answer, read as a model fact: prev.box[j]'s MAC against the image's ZERO. *)
Lemma jn_iff_mac : forall (m : word -> option byte) jj x (v : word),
  jn_mem GSH_it m -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) m) ->
  0 <= jj <= 4 -> x = gF cx fp + GO_PREV + 56 * jj ->
  (v = w64 0 <-> (forall q, 0 <= q < 6 ->
     aview SEGS (w_H W3) m (x + q) = aview SEGS (w_H W3) m (VAL (A_OBJ 6) + q))) ->
  (v = w64 0 <-> Boxreg.bx_mac bs jj = Boxreg.zero6).
Proof.
intros m jj x v HM HRO Hj Hx Hiff. subst x.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MP).
unfold gprev, jms in MP. cbn [ms_mem mkst] in MP.
assert (HBq : forall q, 0 <= q < 6 ->
  (aview SEGS (w_H W3) m (gF cx fp + GO_PREV + 56 * jj + q)
     = aview SEGS (w_H W3) m (VAL (A_OBJ 6) + q) <-> jn_b bs (56 * jj + q) = 0)).
{ intros q Hq. rewrite (jn_zero_bytes m HRO q Hq).
  replace (gF cx fp + GO_PREV + 56 * jj + q) with (gF cx fp + GO_PREV + (56 * jj + q)) by lia.
  rewrite (MP (56 * jj + q) ltac:(unfold REG_SIZE; lia)).
  unfold jn_b. split; intros HH; congruence. }
rewrite Hiff, (jn_mac_zero bs jj HLEN Hj).
split; intros HH q Hq;
  [ exact (proj1 (HBq q Hq) (HH q Hq)) | exact (proj2 (HBq q Hq) (HH q Hq)) ].
Qed.

Lemma jn_bare_seat : forall pc (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc regs mem. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [exact I | split; exact I].
Qed.

Definition JMID (j : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  JINV j regs mem md /\ getr regs 19 = w64 (r + 56 * j) /\ getr regs 23 = w64 (gF cx fp + GO_PREV + 56 * j).

Lemma jn_next : forall j regs mem md,
  (i + 1 < 64 -> gb_from B MT POST (GI_J B MT (i + 1))) -> gb_from B MT POST (GI_X B MT) ->
  (forall regs' mem' md', JINV (j + 1) regs' mem' md' ->
     SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + JP_head)) mem' (seg_rom SEGS)) md') (POST cx)) ->
  JINV j regs mem md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + JP_next)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
intros j regs mem md HJN HXN HNEXT HI.
pose proof (jn_n_small bs HINV) as Hn5.
pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hren32.
destruct HI as (Hj & G2 & G8 & G9 & G3 & G4 & G18 & G24 & G20 & G22 & G25 & G26 & G27 & HJ & HM).
pose proof (proj1 HJ) as HAR.
pose proof jn_sp as (Hal16 & Hceil & H47 & Hsp1 & Hsp32). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & _).
pose proof (jn_sh_range mem md HAR) as (HSL0 & HSL1 & HSdF & HSdsp).
pose proof (jn_bare_seat JP_next regs mem) as HS.
set (E := Eimg (Ereg regs [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EQ : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
  by (intros q rr Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (U24 : bv_unsigned (ew E 24) = gSH cx fp)
  by (rewrite (EQ 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS JBx [] E (mrestrict (w_H W3) mem)) by apply Forall_nil.
assert (HSB : 0 <= SHADOW_OFF + (r + 8 + 56 * j) / 8 /\ SHADOW_OFF + (r + 8 + 56 * j) / 8 + 7 < 2 ^ 64).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (_ & Hr4096 & Hrceil & _ & _).
  change (req_size REG_SIZE) with 288 in Hrceil.
  pose proof (Z.mul_div_le (r + 8 + 56 * j) 8 ltac:(lia)) as M1.
  pose proof (Z.div_pos (r + 8 + 56 * j) 8 ltac:(lia) ltac:(lia)) as M2.
  unfold SHADOW_OFF. lia. }
assert (U25 : bv_unsigned (ew E 25) = 56 * Boxreg.bx_n bs)
  by (rewrite (EQ 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = 56 * j)
  by (rewrite (EQ 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF + (r + 8 + 56 * j) / 8)
  by (rewrite (EQ 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; unfold shadow_of_addr; lia).
paj_run_tok RUN HS HJ SHOK JBspan; [jn_awr U24 |].
lazymatch goal with |- SRr _ _ {| cfg_ms := ?ms; cfg_model := ?md1 |} _ =>
  assert (HM1 : jn_mem GSH_it (ms_mem ms)) by
    (first [ eapply (jn_mem_ro _ _ _ _ _ _ HAR HF ltac:(jn_ro_regions) HM)
           | eapply (jn_mem_ro_raw _ _ _ _ _ _ HAR HF ltac:(jn_ro_regions) HM)
           | eapply (jn_mem_ro _ _ _ _ _ _ HAR HFr ltac:(jn_ro_regions) HM)
           | eapply (jn_mem_ro_raw _ _ _ _ _ _ HAR HFr ltac:(jn_ro_regions) HM) ])
end.
psrr_branch_tok RUN BR HS SHOK JBspan.
- (* bne s9, s6 taken (0x80bd4 -> 0x80aec): one more row *)
  rewrite branch_ne_U, !U_SOff, U25, U22, Z.add_0_r in Hc.
  rewrite (zcanon_id (56 * Boxreg.bx_n bs)) in Hc by (unfold M64; lia).
  rewrite (zcanon_id (56 * j + 56)) in Hc by (unfold M64; lia).
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK JBspan JP_head; [jn_awr U24 |].
  jn_carry (proj1 HJ) HM1 HM2.
  pmkst HS.
  jn_rv HS (2%bv : bv 5) Q2. jn_rv HS (3%bv : bv 5) Q3. jn_rv HS (4%bv : bv 5) Q4.
  jn_rv HS (8%bv : bv 5) Q8. jn_rv HS (9%bv : bv 5) Q9. jn_rv HS (18%bv : bv 5) Q18.
  jn_rv HS (20%bv : bv 5) Q20. jn_rv HS (22%bv : bv 5) Q22. jn_rv HS (24%bv : bv 5) Q24.
  jn_rv HS (25%bv : bv 5) Q25. jn_rv HS (26%bv : bv 5) Q26. jn_rv HS (27%bv : bv 5) Q27.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcx)) _ _) _) _ =>
    let v := eval vm_compute in pcx in change pcx with v end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg' _ ?m' _) ?md') _ =>
    apply (HNEXT rg' m' md'); unfold JINV;
    split; [lia|];
    split; [rewrite Q2, jn_denot_atom, (EQ 2%nat 2%bv eq_refl); exact G2|];
    split; [rewrite Q8, jn_denot_atom, (EQ 8%nat 8%bv eq_refl); exact G8|];
    split; [rewrite Q9, jn_denot_atom, (EQ 9%nat 9%bv eq_refl); exact G9|];
    split; [rewrite Q3, jn_denot_atom, (EQ 3%nat 3%bv eq_refl); exact G3|];
    split; [rewrite Q4, jn_denot_atom, (EQ 4%nat 4%bv eq_refl); exact G4|];
    split; [rewrite Q18, jn_denot_atom, (EQ 18%nat 18%bv eq_refl); exact G18|];
    split; [rewrite Q24, jn_denot_atom, (EQ 24%nat 24%bv eq_refl); exact G24|];
    split; [rewrite Q20, jn_denot_atom, (EQ 20%nat 20%bv eq_refl); exact G20|];
    split; [rewrite Q22, (jn_denot_off E 22%nat (56 * j) 56 U22 ltac:(lia)); f_equal; lia|];
    split; [rewrite Q25, jn_denot_atom, (EQ 25%nat 25%bv eq_refl); exact G25|];
    split; [rewrite Q26, (jn_denot_off E 26%nat _ 7 U26 ltac:(lia)); unfold shadow_of_addr; f_equal;
            replace (r + 8 + 56 * (j + 1)) with ((r + 8 + 56 * j) + 7 * 8) by lia;
            rewrite Z.div_add by lia; lia|];
    split; [rewrite Q27, jn_denot_atom, (EQ 27%nat 27%bv eq_refl); exact G27|];
    split; [exact HJ | exact HM2]
  end.
- (* bne s9, s6 not taken: the last row; 0x80bd8 j 0x80c40 *)
  rewrite branch_ne_U, !U_SOff, U25, U22, Z.add_0_r in Hc.
  rewrite (zcanon_id (56 * Boxreg.bx_n bs)) in Hc by (unfold M64; lia).
  rewrite (zcanon_id (56 * j + 56)) in Hc by (unfold M64; lia).
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK JBspan JP_sh; [jn_awr U24 |].
  jn_carry (proj1 HJ) HM1 HM2.
  pmkst HS.
  jn_rv HS (2%bv : bv 5) Q2. jn_rv HS (3%bv : bv 5) Q3. jn_rv HS (4%bv : bv 5) Q4.
  jn_rv HS (8%bv : bv 5) Q8. jn_rv HS (9%bv : bv 5) Q9. jn_rv HS (18%bv : bv 5) Q18.
  jn_rv HS (20%bv : bv 5) Q20. jn_rv HS (24%bv : bv 5) Q24.
  apply (jn_tail HJN HXN);
  [ rewrite Q2, jn_denot_atom, (EQ 2%nat 2%bv eq_refl); exact G2
  | rewrite Q8, jn_denot_atom, (EQ 8%nat 8%bv eq_refl); exact G8
  | rewrite Q9, jn_denot_atom, (EQ 9%nat 9%bv eq_refl); exact G9
  | rewrite Q3, jn_denot_atom, (EQ 3%nat 3%bv eq_refl); exact G3
  | rewrite Q4, jn_denot_atom, (EQ 4%nat 4%bv eq_refl); exact G4
  | rewrite Q18, jn_denot_atom, (EQ 18%nat 18%bv eq_refl); exact G18
  | rewrite Q24, jn_denot_atom, (EQ 24%nat 24%bv eq_refl); exact G24
  | rewrite Q20, jn_denot_atom, (EQ 20%nat 20%bv eq_refl); exact G20
  | exact HJ | exact HM2 ].
Qed.

(* 0x80bb4 .. 0x80bcc: `beq s11, s6` (j = ren skips the name), else strncmp (prev.box[j].name, r->box[j].name, 32)
   through the strncmp wrapper, whose answer is 0 (the names are kept, llvm_kept), so `bnez a0` at 0x80bc8 does not
   reach the abort block 0x80f60; then the row step jn_next. *)
Lemma jn_ren : forall j regs mem md,
  (i + 1 < 64 -> gb_from B MT POST (GI_J B MT (i + 1))) -> gb_from B MT POST (GI_X B MT) ->
  (forall regs' mem' md', JINV (j + 1) regs' mem' md' ->
     SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + JP_head)) mem' (seg_rom SEGS)) md') (POST cx)) ->
  JMID j regs mem md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + JP_ren)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
intros j regs mem md HJN HXN HNEXT HMID.
pose proof (jn_n_small bs HINV) as Hn5.
pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hren32.
destruct HMID as (HI & G19 & G23).
destruct HI as (Hj & G2 & G8 & G9 & G3 & G4 & G18 & G24 & G20 & G22 & G25 & G26 & G27 & HJ & HM).
pose proof (proj1 HJ) as HAR.
pose proof jn_sp as (Hal16 & Hceil & H47 & Hsp1 & Hsp32). unfold GB_STK in Hceil.
pose proof jn_off as (Hom & Hon & Hob).
pose proof asan_consts as (Hac & _).
pose proof (jn_F mem md HAR) as (HF0 & HFc & HFia & HF32 & HSHeq & HSHp & HFp).
pose proof (jn_sh_range mem md HAR) as (HSL0 & HSL1 & HSdF & HSdsp).
change (fs_frame_bytes GB_CID) with 512 in HF0, HFc, HFia, HSHp, HFp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof pa_B_ok as (HB0 & HB1 & _).
(* JINV j at a later state of the same turn: the twelve registers it names are the seat's, the journal and the
   memory bundle are the new state's. *)
assert (JREG : forall (rg' : bvmap 5 word) m' md',
  getr rg' 2 = getr regs 2 -> getr rg' 3 = getr regs 3 -> getr rg' 4 = getr regs 4 ->
  getr rg' 8 = getr regs 8 -> getr rg' 9 = getr regs 9 -> getr rg' 18 = getr regs 18 ->
  getr rg' 20 = getr regs 20 -> getr rg' 22 = getr regs 22 -> getr rg' 24 = getr regs 24 ->
  getr rg' 25 = getr regs 25 -> getr rg' 26 = getr regs 26 -> getr rg' 27 = getr regs 27 ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 m' md' k ->
  jn_mem GSH_it m' -> JINV j rg' m' md').
{ intros rg' m' md' e2 e3 e4 e8 e9 e18 e20 e22 e24 e25 e26 e27 HJ' HM'. unfold JINV.
  rewrite e2, e3, e4, e8, e9, e18, e20, e22, e24, e25, e26, e27.
  exact (conj Hj (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 (conj G24 (conj G20 (conj G22
    (conj G25 (conj G26 (conj G27 (conj HJ' HM')))))))))))))). }
assert (JPRES : forall (ra rb : bvmap 5 word) (q : bv 5) (z : Z), aregs_preserved ra rb -> z = bv_unsigned q ->
  acallee_saved z -> getr rb q = getr ra q)
  by (intros ra rb q z HPr Hz Hcs; subst z; exact (jn_pres ra rb q HPr Hcs)).
pose proof (jn_bare_seat JP_ren regs mem) as HS.
set (E := Eimg (Ereg regs [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EQ : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
  by (intros q rr Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (U24 : bv_unsigned (ew E 24) = gSH cx fp)
  by (rewrite (EQ 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS JBx [] E (mrestrict (w_H W3) mem)) by apply Forall_nil.
assert (HU240 : bv_unsigned (ew E 240%nat) = VAL 240%nat)
  by (rewrite (HEI 240%nat ltac:(unfold A_TEXT, A_LIM; lia));
      first [reflexivity | (apply unsigned_lit_small; pose proof (pa_val_range 240%nat); lia)]).
assert (HBB : VAL 240%nat = BASE) by reflexivity.
rewrite HBB in HU240.
psrr_branch_tok RUN BR HS SHOK JBspan.
- (* beq s11, s6 taken (0x80bb4 -> 0x80bcc): 56 (ren mod 2^32) = 56 j, the renamed row: no name check *)
  paj_run_to_tok RUNTO HS HJ SHOK JBspan JP_next; [jn_awr U24 |].
  jn_carry HAR HM HM2.
  pmkst HS.
  jn_rv HS (2%bv : bv 5) Q2. jn_rv HS (3%bv : bv 5) Q3. jn_rv HS (4%bv : bv 5) Q4.
  jn_rv HS (8%bv : bv 5) Q8. jn_rv HS (9%bv : bv 5) Q9. jn_rv HS (18%bv : bv 5) Q18.
  jn_rv HS (20%bv : bv 5) Q20. jn_rv HS (22%bv : bv 5) Q22. jn_rv HS (24%bv : bv 5) Q24.
  jn_rv HS (25%bv : bv 5) Q25. jn_rv HS (26%bv : bv 5) Q26. jn_rv HS (27%bv : bv 5) Q27.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcx)) _ _) _) _ =>
    let v := eval vm_compute in pcx in change pcx with v end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg' _ ?m' _) ?md') _ =>
    apply (jn_next j rg' m' md' HJN HXN HNEXT); apply JREG;
    [ rewrite Q2, jn_denot_atom; exact (EQ 2%nat 2%bv eq_refl)
    | rewrite Q3, jn_denot_atom; exact (EQ 3%nat 3%bv eq_refl)
    | rewrite Q4, jn_denot_atom; exact (EQ 4%nat 4%bv eq_refl)
    | rewrite Q8, jn_denot_atom; exact (EQ 8%nat 8%bv eq_refl)
    | rewrite Q9, jn_denot_atom; exact (EQ 9%nat 9%bv eq_refl)
    | rewrite Q18, jn_denot_atom; exact (EQ 18%nat 18%bv eq_refl)
    | rewrite Q20, jn_denot_atom; exact (EQ 20%nat 20%bv eq_refl)
    | rewrite Q22, jn_denot_atom; exact (EQ 22%nat 22%bv eq_refl)
    | rewrite Q24, jn_denot_atom; exact (EQ 24%nat 24%bv eq_refl)
    | rewrite Q25, jn_denot_atom; exact (EQ 25%nat 25%bv eq_refl)
    | rewrite Q26, jn_denot_atom; exact (EQ 26%nat 26%bv eq_refl)
    | rewrite Q27, jn_denot_atom; exact (EQ 27%nat 27%bv eq_refl)
    | exact HJ | exact HM2 ]
  end.
- (* beq s11, s6 not taken: 56 (ren mod 2^32) <> 56 j, so j <> ren and llvm_kept keeps row j's name *)
  assert (Hjr : j <> ren).
  { rewrite branch_eq_U in Hc.
    rewrite (U_atom E 27%nat (56 * (ren mod 2 ^ 32)) (eq_trans (EQ 27%nat 27%bv eq_refl) G27) ltac:(lia)) in Hc.
    rewrite (U_atom E 22%nat (56 * j) (eq_trans (EQ 22%nat 22%bv eq_refl) G22) ltac:(lia)) in Hc.
    apply Z.eqb_neq in Hc. intros Hjr. apply Hc. rewrite <- Hjr, Z.mod_small by lia. reflexivity. }
  clear Hc.
  pose proof (jn_name_eq bs bs' ren j HLEN HLEN' HKEPT Hj Hjr) as Hnm.
  (* 0x80bb8 .. 0x80bc4: a0 = prev.box[j].name, a1 = r->box[j].name, a2 = 32, `jal` the strncmp wrapper *)
  paj_run_tok RUN HS HJ SHOK JBspan; [jn_awr U24 |].
  jn_carry HAR HM HM1.
  jn_rv HS (1%bv : bv 5) R1. jn_rv HS (2%bv : bv 5) R2. jn_rv HS (3%bv : bv 5) R3.
  jn_rv HS (4%bv : bv 5) R4. jn_rv HS (8%bv : bv 5) R8. jn_rv HS (9%bv : bv 5) R9.
  jn_rv HS (10%bv : bv 5) R10. jn_rv HS (11%bv : bv 5) R11. jn_rv HS (12%bv : bv 5) Ra2.
  jn_rv HS (18%bv : bv 5) R18. jn_rv HS (20%bv : bv 5) R20. jn_rv HS (22%bv : bv 5) R22.
  jn_rv HS (24%bv : bv 5) R24. jn_rv HS (25%bv : bv 5) R25. jn_rv HS (26%bv : bv 5) R26.
  jn_rv HS (27%bv : bv 5) R27.
  rewrite (jn_denot_atom E 2%nat), (EQ 2%nat 2%bv eq_refl) in R2.
  rewrite (jn_denot_atom E 3%nat), (EQ 3%nat 3%bv eq_refl) in R3.
  rewrite (jn_denot_atom E 4%nat), (EQ 4%nat 4%bv eq_refl) in R4.
  rewrite (jn_denot_atom E 8%nat), (EQ 8%nat 8%bv eq_refl) in R8.
  rewrite (jn_denot_atom E 9%nat), (EQ 9%nat 9%bv eq_refl) in R9.
  rewrite (jn_denot_atom E 18%nat), (EQ 18%nat 18%bv eq_refl) in R18.
  rewrite (jn_denot_atom E 20%nat), (EQ 20%nat 20%bv eq_refl) in R20.
  rewrite (jn_denot_atom E 22%nat), (EQ 22%nat 22%bv eq_refl) in R22.
  rewrite (jn_denot_atom E 24%nat), (EQ 24%nat 24%bv eq_refl) in R24.
  rewrite (jn_denot_atom E 25%nat), (EQ 25%nat 25%bv eq_refl) in R25.
  rewrite (jn_denot_atom E 26%nat), (EQ 26%nat 26%bv eq_refl) in R26.
  rewrite (jn_denot_atom E 27%nat), (EQ 27%nat 27%bv eq_refl) in R27.
  rewrite (jn_denot_off E 240%nat BASE 3196 HU240 ltac:(lia)) in R1.
  rewrite (jn_denot_lit E 32 ltac:(lia)) in Ra2.
  assert (U23 : bv_unsigned (ew E 23) = gF cx fp + GO_PREV + 56 * j)
    by (rewrite (EQ 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; unfold GO_PREV; lia).
  assert (U19 : bv_unsigned (ew E 19) = r + 56 * j)
    by (rewrite (EQ 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; lia).
  rewrite (jn_denot_off E 23%nat (gF cx fp + GO_PREV + 56 * j) 24 U23 ltac:(unfold GO_PREV; lia)) in R10.
  rewrite (jn_denot_off E 19%nat (r + 56 * j) 24 U19 ltac:(lia)) in R11.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg1 _ ?m1 _) ?md1) _ =>
    assert (HSP1 : spZ rg1 = c_sp1 cx) by (unfold spZ; rewrite R2, G2; apply unsigned_lit_small; lia)
  end.
  eapply SRr_bind;
  [ eapply (jn_strncmp_at (SIGMA BS___interceptor_trampoline_strncmp) ASTRNCMP)
      with (o := c_sp1 cx - spZ (c_regs cx)) (raw := w64 (BASE + JP_sc)) (n := 32)
           (x := gF cx fp + GO_PREV + 56 * j + 24) (y := r + 56 * j + 24)
           (l1 := jn_name bs j) (l2 := jn_name bs j);
    [ exact HJ
    | rewrite HSP1; lia
    | exact Hom | exact Hon | exact Hob
    | rewrite R3, G3; exact Hgp0
    | rewrite R4, G4; exact Htp0
    | exact R1
    | apply ret_ok_codeptr_v; [unfold JP_sc; lia | unfold JP_sc; reflexivity]
    | exact R10 | exact R11 | exact Ra2
    | lia
    | (apply (fm_rom_viewN_of_arodata SEGS B pa_relro_lo pa_relro_hi);
       pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HROb & _);
       eapply arodata_ok_journalP; [exact pa_relro_img | exact RO | exact HJ | exact HROb])
    | exact (HROMO _ _ _ _ _ (proj1 HJ))
    | exact (jn_cstr_prev _ _ j (proj1 HJ) HM1 Hj)
    | exact (jn_cstr_reg _ _ j (proj1 HJ) HM1 Hj Hnm) ]
  | ].
  (* back at 0x80bc8 with a0 = v: the two name fields hold the same C string, so v = 0 *)
  cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HPc & Hv & Hvr & Hiff & Hfr & Hpres2).
  assert (Hv0 : v = 0) by (apply Hiff; unfold fm_strn_eq; reflexivity).
  subst v.
  assert (HM2 : jn_mem GSH_it mem2)
    by (refine (jn_mem_call _ mem2 mem md (c_sp1 cx) HAR eq_refl _ HM1);
        intros a Ha Hna; apply Hfr; [exact Ha | rewrite HSP1; exact Hna]).
  pose proof (eq_trans (JPRES _ _ (2%bv : bv 5) 2 HPc eq_refl ltac:(unfold acallee_saved; lia)) R2) as K2.
  pose proof (eq_trans (JPRES _ _ (3%bv : bv 5) 3 HPc eq_refl ltac:(unfold acallee_saved; lia)) R3) as K3.
  pose proof (eq_trans (JPRES _ _ (4%bv : bv 5) 4 HPc eq_refl ltac:(unfold acallee_saved; lia)) R4) as K4.
  pose proof (eq_trans (JPRES _ _ (8%bv : bv 5) 8 HPc eq_refl ltac:(unfold acallee_saved; lia)) R8) as K8.
  pose proof (eq_trans (JPRES _ _ (9%bv : bv 5) 9 HPc eq_refl ltac:(unfold acallee_saved; lia)) R9) as K9.
  pose proof (eq_trans (JPRES _ _ (18%bv : bv 5) 18 HPc eq_refl ltac:(unfold acallee_saved; lia)) R18) as K18.
  pose proof (eq_trans (JPRES _ _ (20%bv : bv 5) 20 HPc eq_refl ltac:(unfold acallee_saved; lia)) R20) as K20.
  pose proof (eq_trans (JPRES _ _ (22%bv : bv 5) 22 HPc eq_refl ltac:(unfold acallee_saved; lia)) R22) as K22.
  pose proof (eq_trans (JPRES _ _ (24%bv : bv 5) 24 HPc eq_refl ltac:(unfold acallee_saved; lia)) R24) as K24.
  pose proof (eq_trans (JPRES _ _ (25%bv : bv 5) 25 HPc eq_refl ltac:(unfold acallee_saved; lia)) R25) as K25.
  pose proof (eq_trans (JPRES _ _ (26%bv : bv 5) 26 HPc eq_refl ltac:(unfold acallee_saved; lia)) R26) as K26.
  pose proof (eq_trans (JPRES _ _ (27%bv : bv 5) 27 HPc eq_refl ltac:(unfold acallee_saved; lia)) R27) as K27.
  change (w64 (BASE + JP_sc)) with (Z_to_bv 64 (BASE + JP_sc)).
  pose proof (jn_bare_seat JP_sc regs2 mem2) as HS2.
  set (E2 := Eimg (Ereg regs2 [])) in HS2.
  assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2; apply Eimg_env).
  assert (EQ2 : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E2 q = getr regs2 rr)
    by (intros q rr Hq; unfold E2; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (U24b : bv_unsigned (ew E2 24) = gSH cx fp)
    by (rewrite (EQ2 24%nat 24%bv eq_refl), K24, G24; apply unsigned_lit_small; lia).
  assert (SHOK2 : sh_ok SEGS JBx [] E2 (mrestrict (w_H W3) mem2)) by apply Forall_nil.
  psrr_branch_tok RUN BR HS2 SHOK2 JBspan.
  + (* bnez a0 taken (0x80bc8 -> 0x80f60, the abort block): refuted, a0 = 0 *)
    exfalso.
    rewrite branch_ne_U, (U_atom E2 10%nat 0 (eq_trans (EQ2 10%nat 10%bv eq_refl) Hv) ltac:(lia)), U_lit in Hc
      by lia.
    vm_compute in Hc. discriminate Hc.
  + (* bnez a0 not taken: 0x80bcc, the row step *)
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 JBspan JP_next; [jn_awr U24b |].
    jn_carry HAR HM2 HM3.
    pmkst HS2.
    jn_rv HS2 (2%bv : bv 5) Q2. jn_rv HS2 (3%bv : bv 5) Q3. jn_rv HS2 (4%bv : bv 5) Q4.
    jn_rv HS2 (8%bv : bv 5) Q8. jn_rv HS2 (9%bv : bv 5) Q9. jn_rv HS2 (18%bv : bv 5) Q18.
    jn_rv HS2 (20%bv : bv 5) Q20. jn_rv HS2 (22%bv : bv 5) Q22. jn_rv HS2 (24%bv : bv 5) Q24.
    jn_rv HS2 (25%bv : bv 5) Q25. jn_rv HS2 (26%bv : bv 5) Q26. jn_rv HS2 (27%bv : bv 5) Q27.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcx)) _ _) _) _ =>
      let v := eval vm_compute in pcx in change pcx with v end.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg' _ ?m' _) ?md') _ =>
      apply (jn_next j rg' m' md' HJN HXN HNEXT); apply JREG;
      [ rewrite Q2, jn_denot_atom, (EQ2 2%nat 2%bv eq_refl); exact K2
      | rewrite Q3, jn_denot_atom, (EQ2 3%nat 3%bv eq_refl); exact K3
      | rewrite Q4, jn_denot_atom, (EQ2 4%nat 4%bv eq_refl); exact K4
      | rewrite Q8, jn_denot_atom, (EQ2 8%nat 8%bv eq_refl); exact K8
      | rewrite Q9, jn_denot_atom, (EQ2 9%nat 9%bv eq_refl); exact K9
      | rewrite Q18, jn_denot_atom, (EQ2 18%nat 18%bv eq_refl); exact K18
      | rewrite Q20, jn_denot_atom, (EQ2 20%nat 20%bv eq_refl); exact K20
      | rewrite Q22, jn_denot_atom, (EQ2 22%nat 22%bv eq_refl); exact K22
      | rewrite Q24, jn_denot_atom, (EQ2 24%nat 24%bv eq_refl); exact K24
      | rewrite Q25, jn_denot_atom, (EQ2 25%nat 25%bv eq_refl); exact K25
      | rewrite Q26, jn_denot_atom, (EQ2 26%nat 26%bv eq_refl); exact K26
      | rewrite Q27, jn_denot_atom, (EQ2 27%nat 27%bv eq_refl); exact K27
      | exact HJ2 | exact HM3 ]
    end.
Qed.

(* 0x80b9c .. 0x80bb4: `beqz a0` on the first bcmp's answer (prev.box[j].mac against ZERO); when the MAC is not
   zero6, bcmp (prev.box[j].mac, r->box[j].mac, 6) through the bcmp wrapper answers 0 (llvm_kept keeps the MAC), so
   `bnez a0` at 0x80bb0 does not reach the abort block 0x80f60; then jn_ren. *)
Lemma jn_cmp1 : forall j regs mem md,
  (i + 1 < 64 -> gb_from B MT POST (GI_J B MT (i + 1))) -> gb_from B MT POST (GI_X B MT) ->
  (forall regs' mem' md', JINV (j + 1) regs' mem' md' ->
     SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + JP_head)) mem' (seg_rom SEGS)) md') (POST cx)) ->
  JMID j regs mem md ->
  (getr regs 10 = w64 0 <-> Boxreg.bx_mac bs j = Boxreg.zero6) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + JP_b1)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
intros j regs mem md HJN HXN HNEXT HMID H10.
pose proof (jn_n_small bs HINV) as Hn5.
pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hren32.
destruct HMID as (HI & G19 & G23).
assert (Hj5 : 0 <= j <= 4) by (destruct HI as (Hjj & _); lia).
destruct HI as (Hj & G2 & G8 & G9 & G3 & G4 & G18 & G24 & G20 & G22 & G25 & G26 & G27 & HJ & HM).
pose proof (proj1 HJ) as HAR.
pose proof jn_sp as (Hal16 & Hceil & H47 & Hsp1 & Hsp32). unfold GB_STK in Hceil.
pose proof jn_off as (Hom & Hon & Hob).
pose proof asan_consts as (Hac & _).
pose proof (jn_F mem md HAR) as (HF0 & HFc & HFia & HF32 & HSHeq & HSHp & HFp).
pose proof (jn_sh_range mem md HAR) as (HSL0 & HSL1 & HSdF & HSdsp).
change (fs_frame_bytes GB_CID) with 512 in HF0, HFc, HFia, HSHp, HFp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof (jn_bare_seat JP_b1 regs mem) as HS.
set (E := Eimg (Ereg regs [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EQ : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
  by (intros q rr Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (U24 : bv_unsigned (ew E 24) = gSH cx fp)
  by (rewrite (EQ 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS JBx [] E (mrestrict (w_H W3) mem)) by apply Forall_nil.
pose proof pa_B_ok as (HB0 & HB1 & _).
psrr_branch_tok RUN BR HS SHOK JBspan.
- (* 0x80b9c `beqz a0` taken (-> 0x80bb4): prev.box[j].mac = ZERO, no second compare *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK JBspan JP_ren; [jn_awr U24 |].
  jn_carry HAR HM HM2.
  pmkst HS.
  jn_rv HS (2%bv : bv 5) Q2. jn_rv HS (3%bv : bv 5) Q3. jn_rv HS (4%bv : bv 5) Q4.
  jn_rv HS (8%bv : bv 5) Q8. jn_rv HS (9%bv : bv 5) Q9. jn_rv HS (18%bv : bv 5) Q18.
  jn_rv HS (19%bv : bv 5) Q19. jn_rv HS (20%bv : bv 5) Q20. jn_rv HS (22%bv : bv 5) Q22.
  jn_rv HS (23%bv : bv 5) Q23. jn_rv HS (24%bv : bv 5) Q24. jn_rv HS (25%bv : bv 5) Q25.
  jn_rv HS (26%bv : bv 5) Q26. jn_rv HS (27%bv : bv 5) Q27.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcx)) _ _) _) _ =>
    let pv := eval vm_compute in pcx in change pcx with pv end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg' _ ?m' _) ?md') _ =>
    apply (jn_ren j rg' m' md' HJN HXN HNEXT); unfold JMID, JINV;
    split; [|split; [rewrite Q19, jn_denot_atom, (EQ 19%nat 19%bv eq_refl); exact G19
                    |rewrite Q23, jn_denot_atom, (EQ 23%nat 23%bv eq_refl); exact G23]];
    split; [exact Hj|];
    split; [rewrite Q2, jn_denot_atom, (EQ 2%nat 2%bv eq_refl); exact G2|];
    split; [rewrite Q8, jn_denot_atom, (EQ 8%nat 8%bv eq_refl); exact G8|];
    split; [rewrite Q9, jn_denot_atom, (EQ 9%nat 9%bv eq_refl); exact G9|];
    split; [rewrite Q3, jn_denot_atom, (EQ 3%nat 3%bv eq_refl); exact G3|];
    split; [rewrite Q4, jn_denot_atom, (EQ 4%nat 4%bv eq_refl); exact G4|];
    split; [rewrite Q18, jn_denot_atom, (EQ 18%nat 18%bv eq_refl); exact G18|];
    split; [rewrite Q24, jn_denot_atom, (EQ 24%nat 24%bv eq_refl); exact G24|];
    split; [rewrite Q20, jn_denot_atom, (EQ 20%nat 20%bv eq_refl); exact G20|];
    split; [rewrite Q22, jn_denot_atom, (EQ 22%nat 22%bv eq_refl); exact G22|];
    split; [rewrite Q25, jn_denot_atom, (EQ 25%nat 25%bv eq_refl); exact G25|];
    split; [rewrite Q26, jn_denot_atom, (EQ 26%nat 26%bv eq_refl); exact G26|];
    split; [rewrite Q27, jn_denot_atom, (EQ 27%nat 27%bv eq_refl); exact G27|];
    split; [exact HJ | exact HM2]
  end.
- (* 0x80b9c `beqz a0` not taken: prev.box[j].mac <> ZERO; 0x80ba0 .. 0x80bac bcmp (prev.box[j].mac,
     r->box[j].mac, 6) through the bcmp wrapper *)
  assert (Hmac : Boxreg.bx_mac bs j <> Boxreg.zero6).
  { intros Hz. apply H10 in Hz.
    rewrite branch_eq_U, U_SOff, U_SLit, (EQ 10%nat 10%bv eq_refl), Hz in Hc.
    vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK JBspan; [jn_awr U24 |].
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msC end.
  jn_carry HAR HM HM1.
  jn_rv HS (1%bv : bv 5) R1. jn_rv HS (2%bv : bv 5) R2. jn_rv HS (3%bv : bv 5) R3.
  jn_rv HS (4%bv : bv 5) R4. jn_rv HS (8%bv : bv 5) R8. jn_rv HS (9%bv : bv 5) R9.
  jn_rv HS (10%bv : bv 5) R10. jn_rv HS (11%bv : bv 5) R11. jn_rv HS (12%bv : bv 5) Ra2.
  jn_rv HS (18%bv : bv 5) R18. jn_rv HS (19%bv : bv 5) R19. jn_rv HS (20%bv : bv 5) R20.
  jn_rv HS (22%bv : bv 5) R22. jn_rv HS (23%bv : bv 5) R23. jn_rv HS (24%bv : bv 5) R24.
  jn_rv HS (25%bv : bv 5) R25. jn_rv HS (26%bv : bv 5) R26. jn_rv HS (27%bv : bv 5) R27.
  pmkst HS.
  pose proof (proj1 HJ) as HAR1.
  assert (HSP1 : spZ (ms_regs msC) = c_sp1 cx)
    by (unfold spZ; rewrite R2, jn_denot_atom, (EQ 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
  assert (HU240 : bv_unsigned (ew E 240%nat) = VAL 240%nat)
    by (rewrite (HEI 240%nat ltac:(unfold A_TEXT, A_LIM; lia));
        first [reflexivity | (apply unsigned_lit_small; pose proof (pa_val_range 240%nat); lia)]).
  assert (HBB : VAL 240%nat = BASE) by reflexivity.
  rewrite HBB in HU240.
  rewrite (jn_denot_off E 240%nat BASE 3172 HU240 ltac:(lia)) in R1.
  rewrite jn_denot_atom, (EQ 23%nat 23%bv eq_refl), G23 in R10.
  rewrite jn_denot_atom, (EQ 19%nat 19%bv eq_refl), G19 in R11.
  rewrite (jn_denot_lit E 6 ltac:(lia)) in Ra2.
  destruct (jn_prev_ok _ _ _ (gF cx fp + GO_PREV + 56 * j) 6 HAR1 HM1 HSP1
              ltac:(unfold GO_PREV; lia) ltac:(lia) ltac:(unfold GO_PREV; lia))
    as (Xsrc & Xapart & Xmem & Xlo & Xhi & Xra & Xhull).
  destruct (jn_reg_ok _ _ _ (r + 56 * j) 6 HAR1 HM1 HSP1 ltac:(lia) ltac:(lia) ltac:(unfold REG_SIZE; lia))
    as (Ysrc & Yapart & Ymem & Ylo & Yhi & Yra & Yhull).
  eapply SRr_bind;
  [ eapply (jn_bcmp_at (SIGMA BS___interceptor_trampoline_bcmp) ABCMP)
      with (x := gF cx fp + GO_PREV + 56 * j) (y := r + 56 * j) (n := 6)
           (o := c_sp1 cx - spZ (c_regs cx)) (raw := w64 (BASE + JP_b2));
    [ exact HJ
    | rewrite HSP1; lia
    | exact Hom | exact Hon | exact Hob
    | rewrite R3, jn_denot_atom, (EQ 3%nat 3%bv eq_refl), G3; exact Hgp0
    | rewrite R4, jn_denot_atom, (EQ 4%nat 4%bv eq_refl), G4; exact Htp0
    | exact R1
    | apply ret_ok_codeptr_v; [unfold JP_b2; lia | unfold JP_b2; reflexivity]
    | exact R10 | exact R11 | exact Ra2
    | lia
    | exact Xlo | exact Xhi | exact Ylo | exact Yhi
    | exact Xsrc | exact Ysrc | exact Xapart | exact Yapart
    | exact Xmem | exact Ymem
    | exact Xra | intros _; exact Xhull | exact Yra | intros _; exact Yhull ]
  | ].
  cbv beta.
  intros W' c' _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & H10' & Hiff & Hfr & _).
  (* the callee-saved registers of the call are those of the seat *)
  assert (KR : forall (q : bv 5) (nq : nat) (z : Z), Z.of_nat nq = bv_unsigned q -> bv_unsigned q = z ->
            acallee_saved z -> getr (ms_regs msC) q = sv_denot E (SOff nq 0) -> getr regs2 q = getr regs q).
  { intros q nq z Hq Hz Hcs Hr. subst z. rewrite (jn_pres _ _ q HP Hcs), Hr, jn_denot_atom. exact (EQ nq q Hq). }
  assert (K2 : getr regs2 2 = w64 (c_sp1 cx))
    by (rewrite (KR 2%bv 2%nat 2 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R2); exact G2).
  assert (K3 : getr regs2 3 = getr (c_regs cx) 3)
    by (rewrite (KR 3%bv 3%nat 3 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R3); exact G3).
  assert (K4 : getr regs2 4 = getr (c_regs cx) 4)
    by (rewrite (KR 4%bv 4%nat 4 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R4); exact G4).
  assert (K8 : getr regs2 8 = w64 (spZ (c_regs cx)))
    by (rewrite (KR 8%bv 8%nat 8 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R8); exact G8).
  assert (K9 : getr regs2 9 = w64 (c_sp1 cx))
    by (rewrite (KR 9%bv 9%nat 9 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R9); exact G9).
  assert (K18 : getr regs2 18 = w64 SHADOW_OFF)
    by (rewrite (KR 18%bv 18%nat 18 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R18); exact G18).
  assert (K19 : getr regs2 19 = w64 (r + 56 * j))
    by (rewrite (KR 19%bv 19%nat 19 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R19); exact G19).
  assert (K20 : getr regs2 20 = w64 r)
    by (rewrite (KR 20%bv 20%nat 20 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R20); exact G20).
  assert (K22 : getr regs2 22 = w64 (56 * j))
    by (rewrite (KR 22%bv 22%nat 22 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R22); exact G22).
  assert (K23 : getr regs2 23 = w64 (gF cx fp + GO_PREV + 56 * j))
    by (rewrite (KR 23%bv 23%nat 23 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R23); exact G23).
  assert (K24 : getr regs2 24 = w64 (gSH cx fp))
    by (rewrite (KR 24%bv 24%nat 24 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R24); exact G24).
  assert (K25 : getr regs2 25 = w64 (56 * Boxreg.bx_n bs))
    by (rewrite (KR 25%bv 25%nat 25 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R25); exact G25).
  assert (K26 : getr regs2 26 = w64 (shadow_of_addr SHADOW_OFF (r + 8 + 56 * j)))
    by (rewrite (KR 26%bv 26%nat 26 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R26); exact G26).
  assert (K27 : getr regs2 27 = w64 (56 * (ren mod 2 ^ 32)))
    by (rewrite (KR 27%bv 27%nat 27 eq_refl eq_refl ltac:(unfold acallee_saved; lia) R27); exact G27).
  (* bcmp answers 0: prev's MAC bytes (bs) and r's (bs') agree, llvm_kept with a MAC that is not zero6 *)
  assert (Hv0 : v = w64 0).
  { apply (proj2 Hiff). intros q Hq.
    pose proof HM1 as (_ & _ & _ & _ & _ & _ & _ & _ & MREG & MPREV).
    unfold gprev, jms in MPREV. cbn [ms_mem mkst] in MPREV.
    replace (gF cx fp + GO_PREV + 56 * j + q) with (gF cx fp + GO_PREV + (56 * j + q)) by lia.
    replace (r + 56 * j + q) with (r + (56 * j + q)) by lia.
    rewrite (MPREV (56 * j + q) ltac:(unfold REG_SIZE; lia)), (MREG (56 * j + q) ltac:(unfold REG_SIZE; lia)).
    rewrite (jn_mac_eq bs bs' ren j HLEN HLEN' HKEPT Hj Hmac q Hq). reflexivity. }
  pose proof (jn_mem_call _ _ _ _ _ HAR1 HSP1 Hfr HM1) as HM2.
  (* 0x80bb0 `bnez a0`, from a bare seat at the return address *)
  change (w64 (BASE + JP_b2)) with (Z_to_bv 64 (BASE + JP_b2)).
  pose proof (jn_bare_seat JP_b2 regs2 mem2) as HS2.
  set (E2 := Eimg (Ereg regs2 [])) in HS2.
  assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2; apply Eimg_env).
  assert (EQ2 : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E2 q = getr regs2 rr)
    by (intros q rr Hq; unfold E2; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (U24b : bv_unsigned (ew E2 24) = gSH cx fp)
    by (rewrite (EQ2 24%nat 24%bv eq_refl), K24; apply unsigned_lit_small; lia).
  assert (SHOK2 : sh_ok SEGS JBx [] E2 (mrestrict (w_H W3) mem2)) by apply Forall_nil.
  psrr_branch_tok RUN BR HS2 SHOK2 JBspan.
  + (* 0x80bb0 `bnez a0` taken (-> 0x80f60, __asan_handle_no_return + abort): refuted, a0 = v = 0 *)
    exfalso.
    rewrite branch_ne_U, U_SOff, U_SLit, (EQ2 10%nat 10%bv eq_refl), H10', Hv0 in Hc.
    vm_compute in Hc. discriminate Hc.
  + (* 0x80bb0 `bnez a0` not taken: on to 0x80bb4 *)
    clear Hc.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 JBspan JP_ren; [jn_awr U24b |].
    jn_carry HAR HM2 HM3.
    pmkst HS2.
    jn_rv HS2 (2%bv : bv 5) Q2. jn_rv HS2 (3%bv : bv 5) Q3. jn_rv HS2 (4%bv : bv 5) Q4.
    jn_rv HS2 (8%bv : bv 5) Q8. jn_rv HS2 (9%bv : bv 5) Q9. jn_rv HS2 (18%bv : bv 5) Q18.
    jn_rv HS2 (19%bv : bv 5) Q19. jn_rv HS2 (20%bv : bv 5) Q20. jn_rv HS2 (22%bv : bv 5) Q22.
    jn_rv HS2 (23%bv : bv 5) Q23. jn_rv HS2 (24%bv : bv 5) Q24. jn_rv HS2 (25%bv : bv 5) Q25.
    jn_rv HS2 (26%bv : bv 5) Q26. jn_rv HS2 (27%bv : bv 5) Q27.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcx)) _ _) _) _ =>
      let pv := eval vm_compute in pcx in change pcx with pv end.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg' _ ?m' _) ?md') _ =>
      apply (jn_ren j rg' m' md' HJN HXN HNEXT); unfold JMID, JINV;
      split; [|split; [rewrite Q19, jn_denot_atom, (EQ2 19%nat 19%bv eq_refl); exact K19
                      |rewrite Q23, jn_denot_atom, (EQ2 23%nat 23%bv eq_refl); exact K23]];
      split; [exact Hj|];
      split; [rewrite Q2, jn_denot_atom, (EQ2 2%nat 2%bv eq_refl); exact K2|];
      split; [rewrite Q8, jn_denot_atom, (EQ2 8%nat 8%bv eq_refl); exact K8|];
      split; [rewrite Q9, jn_denot_atom, (EQ2 9%nat 9%bv eq_refl); exact K9|];
      split; [rewrite Q3, jn_denot_atom, (EQ2 3%nat 3%bv eq_refl); exact K3|];
      split; [rewrite Q4, jn_denot_atom, (EQ2 4%nat 4%bv eq_refl); exact K4|];
      split; [rewrite Q18, jn_denot_atom, (EQ2 18%nat 18%bv eq_refl); exact K18|];
      split; [rewrite Q24, jn_denot_atom, (EQ2 24%nat 24%bv eq_refl); exact K24|];
      split; [rewrite Q20, jn_denot_atom, (EQ2 20%nat 20%bv eq_refl); exact K20|];
      split; [rewrite Q22, jn_denot_atom, (EQ2 22%nat 22%bv eq_refl); exact K22|];
      split; [rewrite Q25, jn_denot_atom, (EQ2 25%nat 25%bv eq_refl); exact K25|];
      split; [rewrite Q26, jn_denot_atom, (EQ2 26%nat 26%bv eq_refl); exact K26|];
      split; [rewrite Q27, jn_denot_atom, (EQ2 27%nat 27%bv eq_refl); exact K27|];
      split; [exact HJ2 | exact HM3]
    end.
Qed.

Lemma jn_turn : forall j regs mem md,
  (i + 1 < 64 -> gb_from B MT POST (GI_J B MT (i + 1))) -> gb_from B MT POST (GI_X B MT) ->
  (forall regs' mem' md', JINV (j + 1) regs' mem' md' ->
     SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + JP_head)) mem' (seg_rom SEGS)) md') (POST cx)) ->
  JINV j regs mem md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + JP_head)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
intros j regs mem md HJN HXN HNEXT HI.
pose proof (jn_n_small bs HINV) as Hn5.
pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hren32.
assert (Hj5 : 0 <= j <= 4) by (destruct HI as (Hjj & _); lia).
destruct HI as (Hj & G2 & G8 & G9 & G3 & G4 & G18 & G24 & G20 & G22 & G25 & G26 & G27 & HJ & HM).
pose proof (proj1 HJ) as HAR.
pose proof jn_sp as (Hal16 & Hceil & H47 & Hsp1 & Hsp32). unfold GB_STK in Hceil.
pose proof jn_off as (Hom & Hon & Hob).
pose proof asan_consts as (Hac & _).
pose proof (jn_F mem md HAR) as (HF0 & HFc & HFia & HF32 & HSHeq & HSHp & HFp).
pose proof (jn_sh_range mem md HAR) as (HSL0 & HSL1 & HSdF & HSdsp).
change (fs_frame_bytes GB_CID) with 512 in HF0, HFc, HFia, HSHp, HFp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & HRO0 & _).
pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
assert (HRO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem))
  by (eapply arodata_ok_journalP; [exact pa_relro_img | exact RO | exact HJ | exact HRO0]).
pose proof (jn_seat j regs mem md Hj G2 G9 G18 G20 G22 G25 G26 G27 HAR HM) as HS.
set (E := Eimg (Ereg regs (jn_ex j))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EQ : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
  by (intros q rr Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (U24 : bv_unsigned (ew E 24) = gSH cx fp)
  by (rewrite (EQ 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS JBx [] E (mrestrict (w_H W3) mem)) by apply Forall_nil.
assert (EX32 : ew E 32 = w64 (gF cx fp + GO_PREV))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof pa_B_ok as (HB0 & HB1 & _).
pose proof (pa_val_range (A_OBJ 6)) as HVO.
assert (HU240 : bv_unsigned (ew E 240%nat) = VAL 240%nat)
  by (rewrite (HEI 240%nat ltac:(unfold A_TEXT, A_LIM; lia));
      first [reflexivity | (apply unsigned_lit_small; pose proof (pa_val_range 240%nat); lia)]).
assert (HU247 : bv_unsigned (ew E 247%nat) = VAL 247%nat)
  by (rewrite (HEI 247%nat ltac:(unfold A_TEXT, A_OBJ, A_LIM; lia));
      first [reflexivity | (apply unsigned_lit_small; pose proof (pa_val_range 247%nat); lia)]).
assert (HU247' : ew E 247%nat = w64 (VAL (A_OBJ 6)))
  by (unfold w64; rewrite <- (Z_to_bv_bv_unsigned _ (ew E 247%nat)), HU247; reflexivity).
assert (U32 : bv_unsigned (ew E 32) = gF cx fp + GO_PREV)
  by (rewrite (EX32 : ew E 32 = w64 (gF cx fp + GO_PREV)); apply unsigned_lit_small; unfold GO_PREV; lia).
assert (U2 : bv_unsigned (ew E 2) = c_sp1 cx)
  by (rewrite (EQ 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (Hcase : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia.
destruct Hcase as [Ej|[Ej|[Ej|[Ej|Ej]]]]; subst j.
all: paj_run_tok RUN HS HJ SHOK JBspan; [jn_awr U24 |].
all: jn_rv HS (1%bv : bv 5) R1.
all: jn_rv HS (2%bv : bv 5) R2.
all: jn_rv HS (3%bv : bv 5) R3.
all: jn_rv HS (4%bv : bv 5) R4.
all: jn_rv HS (10%bv : bv 5) R10.
all: jn_rv HS (11%bv : bv 5) R11.
all: jn_rv HS (12%bv : bv 5) Ra2.
all: jn_rv HS (19%bv : bv 5) R19.
all: jn_rv HS (23%bv : bv 5) R23.
all: rewrite (jn_denot_atom E 2%nat), (EQ 2%nat 2%bv eq_refl), G2 in R2;
     rewrite (jn_denot_atom E 3%nat), (EQ 3%nat 3%bv eq_refl), G3 in R3;
     rewrite (jn_denot_atom E 4%nat), (EQ 4%nat 4%bv eq_refl), G4 in R4.
all: pmkst HS.
all: lazymatch goal with
     | |- SRr _ _ (mkCfg (mkst ?rg1 _ ?m1 _) ?md1) _ =>
       assert (HAR1 : AR SEGS B ly3 S3 W3 m1 md1) by exact (proj1 HJ);
       assert (HM1 : jn_mem GSH_it m1) by
         (first [ eapply (jn_mem_ro _ _ _ _ _ _ HAR HF ltac:(jn_ro_regions) HM)
                | eapply (jn_mem_ro_raw _ _ _ _ _ _ HAR HF ltac:(jn_ro_regions) HM)
                | eapply (jn_mem_ro _ _ _ _ _ _ HAR HFr ltac:(jn_ro_regions) HM)
                | eapply (jn_mem_ro_raw _ _ _ _ _ _ HAR HFr ltac:(jn_ro_regions) HM) ]);
       assert (HSP1 : spZ rg1 = c_sp1 cx) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia);
       assert (HRO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) m1))
         by (eapply arodata_ok_journalP; [exact pa_relro_img | exact RO | exact HJ | exact HRO0])
     end.
all: assert (U20' : bv_unsigned (ew E 20) = r)
       by (rewrite (EQ 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
all: assert (HBB : VAL 240%nat = BASE) by reflexivity.
all: rewrite HBB in HU240.
all: rewrite (jn_denot_off E 240%nat BASE 3152 HU240 ltac:(lia)) in R1.
all: rewrite (jn_denot_atom E 247%nat), HU247' in R11.
all: rewrite (jn_denot_lit E 6 ltac:(lia)) in Ra2.
all: lazymatch type of R10 with _ = sv_denot _ (SOff _ ?c) =>
       rewrite (jn_denot_off E 32%nat (gF cx fp + GO_PREV) c U32 ltac:(unfold GO_PREV in *; lia)) in R10 end.
all: lazymatch type of R23 with _ = sv_denot _ (SOff _ ?c) =>
       rewrite (jn_denot_off E 32%nat (gF cx fp + GO_PREV) c U32 ltac:(unfold GO_PREV in *; lia)) in R23 end.
all: lazymatch type of R19 with _ = sv_denot _ (SOff _ ?c) =>
       rewrite (jn_denot_off E 20%nat r c U20' ltac:(lia)) in R19 end.
all: lazymatch type of R10 with _ = w64 ?p =>
       destruct (jn_prev_ok _ _ _ p 6 HAR1 HM1 HSP1 ltac:(unfold GO_PREV in *; lia) ltac:(lia)
                  ltac:(unfold GO_PREV in *; lia))
         as (Xsrc & Xapart & Xmem & Xlo & Xhi & Xra & Xhull) end.
all: destruct (jn_zero_ok _ _ _ HAR1 HRO1 HSP1) as (Zsrc & Zapart & Zmem & Zlo & Zhi & Zra & Zhull).
all: eapply SRr_bind;
     [ eapply (jn_bcmp_at (SIGMA BS___interceptor_trampoline_bcmp) ABCMP)
         with (o := c_sp1 cx - spZ (c_regs cx)) (raw := w64 (BASE + JP_b1)) (n := 6);
       [ exact HJ
       | rewrite HSP1; lia
       | exact Hom | exact Hon | exact Hob
       | rewrite R3; exact Hgp0
       | rewrite R4; exact Htp0
       | exact R1
       | apply ret_ok_codeptr_v; [unfold JP_b1; lia | unfold JP_b1; reflexivity]
       | exact R10 | exact R11 | exact Ra2
       | lia
       | exact Xlo | exact Xhi | exact Zlo | exact Zhi
       | exact Xsrc | exact Zsrc | exact Xapart | exact Zapart
       | exact Xmem | exact Zmem
       | exact Xra | intros _; exact Xhull | exact Zra | intros _; exact Zhull ]
     | ].
all: cbv beta; intros W2 c2 _ (Heq & regs2 & mem2 & md2 & v & Hc2 & HJ2 & HP2 & Hv & Hiff & Hfr & Hpres2);
     subst W2; subst c2.
all: jn_rv HS (8%bv : bv 5) R8. all: jn_rv HS (9%bv : bv 5) R9. all: jn_rv HS (18%bv : bv 5) R18.
all: jn_rv HS (20%bv : bv 5) R20. all: jn_rv HS (22%bv : bv 5) R22. all: jn_rv HS (24%bv : bv 5) R24.
all: jn_rv HS (25%bv : bv 5) R25. all: jn_rv HS (26%bv : bv 5) R26. all: jn_rv HS (27%bv : bv 5) R27.
all: rewrite (jn_denot_atom E 8%nat), (EQ 8%nat 8%bv eq_refl), G8 in R8;
     rewrite (jn_denot_atom E 9%nat), (EQ 9%nat 9%bv eq_refl), G9 in R9;
     rewrite (jn_denot_atom E 18%nat), (EQ 18%nat 18%bv eq_refl), G18 in R18;
     rewrite (jn_denot_atom E 20%nat), (EQ 20%nat 20%bv eq_refl), G20 in R20;
     rewrite (jn_denot_atom E 24%nat), (EQ 24%nat 24%bv eq_refl), G24 in R24;
     rewrite (jn_denot_atom E 38%nat) in R25; rewrite (jn_denot_atom E 39%nat) in R27.
all: assert (EX38 : ew E 38 = w64 (56 * Boxreg.bx_n bs))
       by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
all: assert (EX39 : ew E 39 = w64 (56 * (ren mod 2 ^ 32)))
       by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
all: rewrite EX38 in R25; rewrite EX39 in R27.
all: lazymatch type of R22 with _ = sv_denot _ (SLit ?c) =>
       rewrite (jn_denot_lit E c ltac:(lia)) in R22 end.
all: lazymatch type of R26 with _ = sv_denot _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff _ ?c) _) _) =>
       rewrite (jn_U_shadow E 20%nat r c SHADOW_OFF
         ltac:(rewrite (EQ 20%nat 20%bv eq_refl); exact G20) ltac:(rewrite (EQ 18%nat 18%bv eq_refl); exact G18)
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)
         ltac:(pose proof (Z.mul_div_le (r + c) 8 ltac:(lia)); pose proof (Z.div_pos (r + c) 8 ltac:(lia) ltac:(lia));
               unfold SHADOW_OFF; lia)) in R26 end.
all: rewrite HSP1 in Hfr.
all: assert (HM2 : jn_mem GSH_it mem2)
       by (apply (jn_mem_call _ mem2 _ _ (c_sp1 cx) HAR1 eq_refl Hfr HM1)).
all: apply (jn_cmp1 _ regs2 mem2 md2 HJN HXN HNEXT);
     [ unfold JMID, JINV;
       split;
       [ split; [lia|];
         split; [rewrite (jn_pres _ regs2 (2%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R2|];
         split; [rewrite (jn_pres _ regs2 (8%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R8|];
         split; [rewrite (jn_pres _ regs2 (9%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R9|];
         split; [rewrite (jn_pres _ regs2 (3%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R3|];
         split; [rewrite (jn_pres _ regs2 (4%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R4|];
         split; [rewrite (jn_pres _ regs2 (18%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R18|];
         split; [rewrite (jn_pres _ regs2 (24%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R24|];
         split; [rewrite (jn_pres _ regs2 (20%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R20|];
         split; [rewrite (jn_pres _ regs2 (22%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R22|];
         split; [rewrite (jn_pres _ regs2 (25%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R25|];
         split; [rewrite (jn_pres _ regs2 (26%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)), R26;
                 apply jn_shadow_eq; lia|];
         split; [rewrite (jn_pres _ regs2 (27%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R27|];
         split; [exact HJ2 | exact HM2] |];
       split;
       [ rewrite (jn_pres _ regs2 (19%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R19
       | rewrite (jn_pres _ regs2 (23%bv : bv 5) HP2 ltac:(unfold acallee_saved; vm_compute (bv_unsigned _); lia)); exact R23 ]
     | rewrite Hv;
       lazymatch type of Hiff with
       | _ <-> (forall q, _ -> aview _ _ _ (?X + q) = _) =>
         refine (jn_iff_mac _ _ X _ HM1 HRO1 _ _ Hiff); lia
       end ].
Qed.

(* The whole check_kept loop: at most bx_n bs <= 5 turns, one row each. *)
Lemma jn_loop : forall (f : nat) j regs mem md,
  (i + 1 < 64 -> gb_from B MT POST (GI_J B MT (i + 1))) -> gb_from B MT POST (GI_X B MT) ->
  (Z.to_nat (Boxreg.bx_n bs - j) <= f)%nat -> JINV j regs mem md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + JP_head)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
induction f as [|f IH]; intros j regs mem md HJN HXN Hf HI.
- exfalso. destruct HI as (Hj & _). lia.
- apply (jn_turn j regs mem md HJN HXN); [|exact HI].
  intros regs' mem' md' HI'. apply (IH (j + 1) regs' mem' md' HJN HXN); [|exact HI'].
  destruct HI' as (Hj' & _). destruct HI as (Hj & _). lia.
Qed.

(* 0x80ac0 .. 0x80aec, after check returns: prev.n is read at F + 0x40 + 280 (slot 0x78, no shadow test), `blez`
   skips the loop when it is 0 (0x80c40, jn_tail); else s6 = 0, s9 = 56 n, s11 = 56 ren32 and s10 = the slot 0x38
   cursor, which is JINV 0 at the head 0x80aec. *)
Lemma jn_enter : forall (regs : bvmap 5 word) mem md,
  (i + 1 < 64 -> gb_from B MT POST (GI_J B MT (i + 1))) -> gb_from B MT POST (GI_X B MT) ->
  (forall j regs' mem' md', JINV j regs' mem' md' ->
     SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + JP_head)) mem' (seg_rom SEGS)) md') (POST cx)) ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 24 = w64 (gSH cx fp) -> getr regs 20 = w64 r ->
  getr regs 21 = w64 (ren mod 2 ^ 32) ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 mem md k ->
  jn_mem GSH_it mem ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + JP_ret)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs mem md HJN HXN HLOOP G2 G8 G9 G3 G4 G18 G24 G20 G21 HJ HM.
pose proof (jn_n_small bs HINV) as Hn5.
pose proof (Z.mod_pos_bound ren (2 ^ 32) ltac:(lia)) as Hren32.
pose proof (proj1 HJ) as HAR.
pose proof jn_sp as (Hal16 & Hceil & H47 & Hsp1 & Hsp32). unfold GB_STK in Hceil.
pose proof asan_consts as (Hac & _).
pose proof (jn_F mem md HAR) as (HF0 & HFc & HFia & HF32 & HSHeq & HSHp & HFp).
pose proof (jn_sh_range mem md HAR) as (HSL0 & HSL1 & HSdF & HSdsp).
change (fs_frame_bytes GB_CID) with 512 in HF0, HFc, HFia, HSHp, HFp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR HRIN) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
pose proof HM as (_ & _ & _ & (_ & _ & _ & MF78 & _) & (_ & _ & MR38 & _) & _ & _ & _ & _ & MPREV).
assert (Hg8 : gF cx fp mod 8 = 0).
{ apply Z.mod_divide in HF32; [|lia]. apply Z.mod_divide; [lia|].
  destruct HF32 as [q Hq]. exists (4 * q). lia. }
assert (Hn280 : jn_u bs 280 = Boxreg.bx_n bs).
{ unfold Boxreg.bx_n in *. apply jn_u_of_rd4; [lia | rewrite HLEN; lia | lia]. }
assert (Hsr8 : 0 <= shadow_of_addr SHADOW_OFF (r + 8) < 2 ^ 64).
{ unfold shadow_of_addr, SHADOW_OFF.
  pose proof (Z.div_pos (r + 8) 8 ltac:(lia) ltac:(lia)) as Dp.
  pose proof (Z.mul_div_le (r + 8) 8 ltac:(lia)) as Dm. lia. }
set (E := Eimg (Ereg regs [w64 (gF cx fp + GO_PREV); w64 (shadow_of_addr SHADOW_OFF (r + 8));
                           w64 (Boxreg.bx_n bs)])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EQ : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
  by (intros q rr Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (F32 : ew E 32 = w64 (gF cx fp + GO_PREV))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (F33 : ew E 33 = w64 (shadow_of_addr SHADOW_OFF (r + 8)))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (F34 : ew E 34 = w64 (Boxreg.bx_n bs))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EQ 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = r)
  by (rewrite (EQ 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = ren mod 2 ^ 32)
  by (rewrite (EQ 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = gSH cx fp)
  by (rewrite (EQ 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = gF cx fp + GO_PREV)
  by (rewrite F32; apply unsigned_lit_small; unfold GO_PREV; lia).
assert (U34 : bv_unsigned (ew E 34) = Boxreg.bx_n bs)
  by (rewrite F34; apply unsigned_lit_small; lia).
(* The seat: the spill slots 0x38 (the cursor, atom 33) and 0x78 (prev, atom 32) at s1, and prev.n (atom 34). *)
assert (HS : st_ok_pi SEGS VAL E
  (mkSS JP_ret sr_atoms
     [YP09.mkRegion (Some 9%nat) 0 152 0 0
        [YP09.mkChunk 0x38 (CVal 8 (SOff 33%nat 0)); YP09.mkChunk 0x78 (CVal 8 (SOff 32%nat 0))];
      YP09.mkRegion (Some 32%nat) 0 288 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 34%nat 0))]]
     None (mkFacts [(20%nat, mkAF 4096 (2 ^ 47) 4); (32%nat, mkAF 4096 (2 ^ 47) 3); (34%nat, mkAF 0 5 0)]
             [] []))
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + JP_ret)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) (c_sp1 cx) 0x38 8%N (SOff 33%nat 0)
                 (shadow_of_addr SHADOW_OFF (r + 8))).
        -- cbn [sv_denot]. rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- change (Z.of_N 8) with 8. lia.
        -- apply (val_mem_of_rdword SEGS (w_H W3) mem). exact MR38.
      * apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) (c_sp1 cx) 0x78 8%N (SOff 32%nat 0)
                 (gF cx fp + GO_PREV)).
        -- cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold GO_PREV. lia.
        -- change (Z.of_N 8) with 8. lia.
        -- apply (val_mem_of_rdword SEGS (w_H W3) mem). exact MF78.
    + unfold YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U32. split; [unfold GO_PREV; lia|]. split; [unfold GO_PREV; lia|]. split; [intros o Ho; lia|].
      assert (MPB : forall q, 0 <= q < REG_SIZE ->
        aview SEGS (w_H W3) mem (gF cx fp + GO_PREV + q) = Some (jn_b bs q)) by exact MPREV.
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem) (gF cx fp + GO_PREV) 280 4%N (SOff 34%nat 0)
               (Boxreg.bx_n bs)).
      * cbn [sv_denot]. rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      * change (Z.of_N 4) with 4. lia.
      * rewrite <- Hn280. apply (jn_val4 mem (gF cx fp + GO_PREV) bs 280 MPB); unfold REG_SIZE; lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold GO_PREV. repeat split; try exact I; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U32, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold ASAN_CEIL, GO_PREV in *.
    assert (A8 : (gF cx fp + 64) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hg8; reflexivity).
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia; first [exact Hr16 | exact A8]. }
assert (SHOK : sh_ok SEGS JBx [] E (mrestrict (w_H W3) mem)) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK JBspan; [jn_awr U24 |].
lazymatch goal with |- SRr _ _ {| cfg_ms := ?ms; cfg_model := ?md1 |} _ =>
  assert (HM1 : jn_mem GSH_it (ms_mem ms)) by
    (first [ eapply (jn_mem_ro _ _ _ _ _ _ HAR HF ltac:(jn_ro_regions) HM)
           | eapply (jn_mem_ro_raw _ _ _ _ _ _ HAR HF ltac:(jn_ro_regions) HM)
           | eapply (jn_mem_ro _ _ _ _ _ _ HAR HFr ltac:(jn_ro_regions) HM)
           | eapply (jn_mem_ro_raw _ _ _ _ _ _ HAR HFr ltac:(jn_ro_regions) HM) ])
end.
psrr_branch_tok RUN BR HS SHOK JBspan.
- (* blez a0 taken (0x80ac8 -> 0x80c40): prev.n = 0, no row to check *)
  paj_run_to_tok RUNTO HS HJ SHOK JBspan JP_sh; [jn_awr U24 |].
  jn_carry (proj1 HJ) HM1 HM2.
  pmkst HS.
  jn_rv HS (2%bv : bv 5) Q2. jn_rv HS (3%bv : bv 5) Q3. jn_rv HS (4%bv : bv 5) Q4.
  jn_rv HS (8%bv : bv 5) Q8. jn_rv HS (9%bv : bv 5) Q9. jn_rv HS (18%bv : bv 5) Q18.
  jn_rv HS (20%bv : bv 5) Q20. jn_rv HS (24%bv : bv 5) Q24.
  apply (jn_tail HJN HXN);
  [ rewrite Q2, jn_denot_atom, (EQ 2%nat 2%bv eq_refl); exact G2
  | rewrite Q8, jn_denot_atom, (EQ 8%nat 8%bv eq_refl); exact G8
  | rewrite Q9, jn_denot_atom, (EQ 9%nat 9%bv eq_refl); exact G9
  | rewrite Q3, jn_denot_atom, (EQ 3%nat 3%bv eq_refl); exact G3
  | rewrite Q4, jn_denot_atom, (EQ 4%nat 4%bv eq_refl); exact G4
  | rewrite Q18, jn_denot_atom, (EQ 18%nat 18%bv eq_refl); exact G18
  | rewrite Q24, jn_denot_atom, (EQ 24%nat 24%bv eq_refl); exact G24
  | rewrite Q20, jn_denot_atom, (EQ 20%nat 20%bv eq_refl); exact G20
  | exact HJ | exact HM2 ].
- (* blez a0 not taken: 0 < prev.n; s6, s9, s11 and s10 are set, then the loop head 0x80aec *)
  assert (Hnpos : 0 < Boxreg.bx_n bs).
  { destruct (Z.eq_dec (Boxreg.bx_n bs) 0) as [Hn0 | Hn0]; [|lia].
    exfalso. rewrite (jn_denot_lit E 0 ltac:(lia)), (jn_denot_atom E 34%nat), F34, Hn0 in Hc.
    vm_compute in Hc. discriminate Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK JBspan JP_head; [jn_awr U24 |].
  jn_carry (proj1 HJ) HM1 HM2.
  pmkst HS.
  jn_rv HS (2%bv : bv 5) Q2. jn_rv HS (3%bv : bv 5) Q3. jn_rv HS (4%bv : bv 5) Q4.
  jn_rv HS (8%bv : bv 5) Q8. jn_rv HS (9%bv : bv 5) Q9. jn_rv HS (18%bv : bv 5) Q18.
  jn_rv HS (20%bv : bv 5) Q20. jn_rv HS (22%bv : bv 5) Q22. jn_rv HS (24%bv : bv 5) Q24.
  jn_rv HS (25%bv : bv 5) Q25. jn_rv HS (26%bv : bv 5) Q26. jn_rv HS (27%bv : bv 5) Q27.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcx)) _ _) _) _ =>
    let v := eval vm_compute in pcx in change pcx with v end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg' _ ?m' _) ?md') _ =>
    apply (HLOOP 0 rg' m' md'); unfold JINV;
    split; [lia|];
    split; [rewrite Q2, jn_denot_atom, (EQ 2%nat 2%bv eq_refl); exact G2|];
    split; [rewrite Q8, jn_denot_atom, (EQ 8%nat 8%bv eq_refl); exact G8|];
    split; [rewrite Q9, jn_denot_atom, (EQ 9%nat 9%bv eq_refl); exact G9|];
    split; [rewrite Q3, jn_denot_atom, (EQ 3%nat 3%bv eq_refl); exact G3|];
    split; [rewrite Q4, jn_denot_atom, (EQ 4%nat 4%bv eq_refl); exact G4|];
    split; [rewrite Q18, jn_denot_atom, (EQ 18%nat 18%bv eq_refl); exact G18|];
    split; [rewrite Q24, jn_denot_atom, (EQ 24%nat 24%bv eq_refl); exact G24|];
    split; [rewrite Q20, jn_denot_atom, (EQ 20%nat 20%bv eq_refl); exact G20|];
    split; [rewrite Q22, (jn_denot_lit E 0 ltac:(lia)); reflexivity|];
    split; [rewrite Q25, denot_lit_U; change (SMd M_MUL (SOff 34%nat 0) (SLit 56)) with (mono 34 56);
            rewrite mono_sound, U34, Z.mod_small by (unfold M64; lia); reflexivity|];
    split; [rewrite Q26, jn_denot_atom, F33; replace (r + 8 + 56 * 0) with (r + 8) by lia; reflexivity|];
    split; [rewrite Q27, denot_lit_U; change (SMd M_MUL (SOff 21%nat 0) (SLit 56)) with (mono 21 56);
            rewrite mono_sound, U21, Z.mod_small by (unfold M64; lia); reflexivity|];
    split; [exact HJ | exact HM2]
  end.
Qed.

End d.

(* The phase: from the cut K (0x80ab4), check (r, fabric), then jn_enter with the loop jn_loop. *)
Theorem gb_join : forall i0,
  (i0 + 1 < 64 -> gb_from B MT POST (GI_J B MT (i0 + 1))) -> gb_from B MT POST (GI_X B MT) ->
  gb_from B MT POST (GI_K B MT i0).
Proof.
intros i0 HJN HXN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HK.
destruct HK as (r & bs & bs' & ren & pos & HBODY & Hi & Hk & Hacc & HBLK & (HRIN & HLEN' & HRB) & HPREV &
  HINV & HINV' & HFAB & HKEPT & HREN & G20 & G21 & G25 & HSR & HCUR & H68).
pose proof (proj1 (proj2 HJ)) as HLY.
assert (HLEN : length bs = 288%nat) by (destruct HINV as ((HL & _) & _); exact HL).
destruct HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & (G2 & G8 & G9 & G3 & G4 & G18 & G24) &
  HSV & HSH & Hlen & HFLW & HFRS & HIN).
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & HRO0 & Hsp1 & _).
pose proof HPRE as (_ & _ & Hra40 & Hgp0 & Htp0 & Hstk & _ & Hch0 & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (Hac & _).
pose proof pa_B_ok as (HB0 & HB1 & _).
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
unfold GB_STK in Hslo.
(* The realigned stack pointer s1 and its offset from the caller's sp. *)
assert (Hx : 0 <= spZ (c_regs cx) + -256) by lia.
pose proof (Z.div_mod (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hmp.
assert (HspA : spZ (c_regs cx) - 288 < c_sp1 cx <= spZ (c_regs cx) - 256) by (rewrite Hsp1; lia).
assert (Hsp32 : c_sp1 cx mod 32 = 0) by (rewrite Hsp1, Z.mul_comm, Z_mod_mult; reflexivity).
assert (Hom : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ pose proof Hal16 as A1. pose proof Hsp32 as A2.
  apply Z.mod_divide; [lia|]. apply Z.mod_divide in A1; [|lia]. apply Z.mod_divide in A2; [|lia].
  destruct A1 as [q1 Hq1]. destruct A2 as [q2 Hq2]. exists (2 * q2 - q1). lia. }
assert (Hal8 : spZ (c_regs cx) mod 8 = 0).
{ pose proof Hal16 as A1. apply Z.mod_divide; [lia|]. apply Z.mod_divide in A1; [|lia].
  destruct A1 as [q Hq]. exists (2 * q). lia. }
(* The memory bundle jn_enter carries, from the cut's facts. *)
assert (HM3 : jn_mem cx fp W3 r pos i0 bs bs' GSH_it (ms_mem ms3)).
{ unfold jn_mem. split; [exact HSV|]. split; [exact HSH|]. split; [exact HFLW|]. split; [exact HFRS|].
  split; [exact HSR|]. split; [exact HCUR|]. split; [exact H68|]. split; [exact HIN|].
  split; [exact HRB | exact HPREV]. }
assert (EMS : forall ms : machine_state, ms_pc_val ms = w64 (BASE + GP_K) -> ms_resv ms = None ->
  ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + GP_K)) (ms_mem ms) (seg_rom SEGS)).
{ intros [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem].
  intros -> -> -> -> -> ->. reflexivity. }
rewrite (EMS ms3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr). clear EMS.
(* 0x80ab4 .. 0x80abc: a0 = r, a1 = the fabric, `jal check`. *)
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [])) (mkSS GP_K sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_K)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [exact I | split; exact I]. }
set (E := Eimg (Ereg (ms_regs ms3) [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
  by (intros q rr Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (SHOK : sh_ok SEGS JBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose proof (paj_run B LAWS) as RUN.
paj_run_tok RUN HS HJ SHOK JBspan; [apply awr_ok_nil |].
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms1 end.
(* The three instructions wrote nothing. *)
assert (M1 : forall a, aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a.
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ms1)) |- _ =>
    cbn [ms_mem mkst] in HFx; unfold aview, mbyte;
    rewrite (HFx (Z_to_bv 64 a)); [reflexivity | intros (rg & Hin & _); vm_compute in Hin; destruct Hin] end. }
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (24%bv : bv 5) Q24.
rewrite (EE 2%nat 2%bv eq_refl) in Q2. rewrite (EE 3%nat 3%bv eq_refl) in Q3.
rewrite (EE 4%nat 4%bv eq_refl) in Q4. rewrite (EE 8%nat 8%bv eq_refl) in Q8.
rewrite (EE 9%nat 9%bv eq_refl) in Q9. rewrite (EE 20%nat 20%bv eq_refl) in Q10.
rewrite (EE 25%nat 25%bv eq_refl) in Q11. rewrite (EE 18%nat 18%bv eq_refl) in Q18.
rewrite (EE 20%nat 20%bv eq_refl) in Q20. rewrite (EE 21%nat 21%bv eq_refl) in Q21.
rewrite (EE 24%nat 24%bv eq_refl) in Q24.
pmkst HS. rewrite pa_sigma_check.
(* check (r, fabric): tcheck_spec through cl_callS; the call keeps the bytes the phase reads. *)
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs ms1) (ms_mem ms1) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
    (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k CHECK_STK [] 0 (c_sp1 cx - spZ (c_regs cx))
    (getr (ms_regs ms1) 1) (gch cx)
    (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
       Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
       (forall q, 0 <= q < REG_SIZE ->
          aview SEGS (w_H W2) mem2 (r + q) = Some (bv_unsigned (nth (Z.to_nat q) bs' (Z_to_bv 8 0)))))
    HJ).
  - unfold spZ at 1. rewrite Q2, G2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - unfold CHECK_STK, ESTACK. lia.
  - unfold CHECK_STK, ESTACK, GB_STK. lia.
  - rewrite Q3, G3. exact Hgp0.
  - rewrite Q4, G4. exact Htp0.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - (* the caller chain at s1: s0 is the caller's sp, whose frame record the prologue saved *)
    replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
    replace (s0Z (ms_regs ms1)) with (spZ (c_regs cx))
      by (unfold s0Z; rewrite Q8, G8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    assert (HK8 : forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
      aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H (c_W cx)) (c_mem cx) a)
      by (intros a Ha; apply F1; lia).
    assert (H8 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
    { rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms1)))
        by (intros q _; apply M1).
      exact (proj1 HSV). }
    assert (H16 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
    { rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms1)))
        by (intros q _; apply M1).
      pose proof (proj2 HSV 0 ltac:(lia)) as S0. rewrite Z.mul_0_r, Z.sub_0_r in S0. exact S0. }
    unfold gch.
    destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
    + apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) (ms_mem ms1))
               (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] (c_sp1 cx) Hch0 ltac:(lia)
               HK8 H8 H16 Hra40); [lia | exact Hal8 | lia | lia].
    + left. split; [right; left; lia | reflexivity].
  - intros HPRE1.
    assert (HRO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms1)))
      by (eapply arodata_ok_journalP; [exact pa_relro_img | exact RO | exact HJ | exact HRO0]).
    eapply SRr_mono.
    + exact (TCHECK ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ (gch cx) r (Boxreg.bx_fabric bs) bs' BX_G HPRE1 HRO1
        ltac:(rewrite Q10, G20; reflexivity) ltac:(rewrite Q11, G25; reflexivity) HRIN
        ltac:(intros q Hq; rewrite M1; exact (HRB q Hq)) (proj1 HINV') HFAB HISV HGLOB HZB
        ltac:(unfold BX_G; left; reflexivity) HZ1 HZ2 HMCH).
    + cbv beta. intros W' c' _ HQ. exact HQ.
  - intros a (rgx & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & _ & _)).
rewrite Z.add_0_r in HJ2.
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
assert (KP : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr (ms_regs ms1) rr).
{ intros rr Hr. pose proof (HP2 (bv_unsigned rr) Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
assert (HM2 : jn_mem cx fp W3 r pos i0 bs bs' GSH_it mem2).
{ apply (jn_mem_keep cx fp W3 r pos i0 bs bs' HB HLEN HLEN' Hi GSH_it (ms_mem ms3) mem2 HM3).
  - intros a Ha. rewrite <- (M1 a).
    exact (jn_keep_call cx fp ly3 S3 W3 r i0 bs bs' HB HLY HFR HRIN HBLK HLEN HLEN' Hi CHECK_STK (ms_mem ms1) _
             mem2 md2 0 HJc a Ha).
  - vm_compute. lia. }
rewrite Q1.
(* 0x80ac0: jn_enter, with the loop jn_loop at its head. *)
apply (jn_enter cx fp k acc ly3 S3 W3 r ren pos i0 bs bs' HB HLY HFR HRIN HBLK HLEN HLEN' HINV HINV' HFAB
  Hi Hk Hacc HMO regs2 mem2 md2 HJN HXN).
- intros j regs' mem' md' HI'.
  eapply jn_loop.
  all: first [ exact HI' | idtac ].
  all: first [ exact (le_n _) | eassumption ].
- rewrite (KP 2%bv ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)), Q2. exact G2.
- rewrite (KP 8%bv ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)), Q8. exact G8.
- rewrite (KP 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)), Q9. exact G9.
- rewrite (KP 3%bv ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)), Q3. exact G3.
- rewrite (KP 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), Q4. exact G4.
- rewrite (KP 18%bv ltac:(change (bv_unsigned (18%bv : bv 5)) with 18; unfold acallee_saved; lia)), Q18.
  exact G18.
- rewrite (KP 24%bv ltac:(change (bv_unsigned (24%bv : bv 5)) with 24; unfold acallee_saved; lia)), Q24.
  exact G24.
- rewrite (KP 20%bv ltac:(change (bv_unsigned (20%bv : bv 5)) with 20; unfold acallee_saved; lia)), Q20.
  exact G20.
- rewrite (KP 21%bv ltac:(change (bv_unsigned (21%bv : bv 5)) with 21; unfold acallee_saved; lia)), Q21.
  exact G21.
- exact HJ2.
- exact HM2.
Qed.

End c.
End b.
End a.
