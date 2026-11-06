(* fs program part, lane CRT, lane L7, image B: the LOOP of check_round_trip's segment 7 - `canonical(input, same)`
   inlined from fuzz_state.c:296 - on the pinned fs.asan-ubsan (image tfibsegs, build B, sha256 5ac5ce0954f8...), head
   0x8210c, exit 0x82180 (crt_INV_81fb8 -> crt_INV_82028; the A names keep their A pcs, the content is B's).

   The B twin of a working branch 2b7e9117c25 proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_loop7.v
   (A 0x81fb8 -> 0x82028): the same Definition / Lemma names and statement shapes, every pc, register and constant
   RE-MEASURED on B (capstone listing (internal path)), over lib/B/FSH_crt_base.v (B base
   v27, crt_stable7E, crt_STK) and lib/B/FSH_crt_site.v (crt_J, crt_F_facts). A new file: no licence lines.
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 2b7e9117c25 lib/A/FSH_crt_loop7.v)
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from c6275044faa) - the STK value
   is read through the base's crt_STK_eq (A base v27's pattern), never a literal.
   The A file's own port source carries over: d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_loops.v
   (cs_pre / cs_j / cs_facts :806-809, crt_canonical :1032, ws_bit :717; checker verdict a Theorem Labs lane on that hit), re-keyed
   to the lane boundaries, and what each became:
   - cs_pre / cs_j (:806-807)  -> l7_pre / l7_j: after i trips the output holds b64_strip of the first i text bytes,
     the cursor is t + i and the count is its length.
   - cs_facts (:808-809)       -> l7_at, in the S0 forms (ajournal over `unpoison U mem`, ARU, zbytes_at).
   - crt_canonical (:1032)     -> crt_l7 (continuation form, so it composes with the base's crt_from) and the three
     leaf lemmas l7_keep_done / l7_skip_done / l7_fin.
   - ws_bit (:717)             -> l7_ws_bit, the same bit test on the same constant 4294977024 (0x100002600), with the
     engine-side branch conditions l7_bit_val / l7_bit_eqb / l7_zero_eqb / l7_gt32_ltb added on top of it.
   The ASan run mechanics follow the kit (lib/B/FSW_K's token runs) and cgif's loop pattern (proofs/cgif/cgif_file_fuzzer/
   lib/A/ACik.v .. ACix.v: a concrete-register statement at the loop head, one trip = head -> head, induction on the
   trips left).

   MEASURED on the pinned fs.asan-ubsan (capstone, RISCV64+C, backward branches of 0x81b9c..0x8266c): segment 7's
   back-edges are ONE loop with internal branches. Only 0x82138 -> 0x8210c re-enters the header 0x8210c; 0x82164 ->
   0x82130, 0x82170 -> 0x8211c and 0x82178 -> 0x8215c land strictly inside the body below the header and are the store
   tail's join and the returns of the two inline partial-granule slow paths (0x82168 / 0x82174), so the loop is
   single-entry with one back-edge. The pre-header 0x820c8 .. 0x82108 sets a1 = 0, a2 = ~s8, a3 = s9 - 1, a4 = 32,
   a5 = -1, a6 = 0x100002600 and falls through into the header.

   The loop body, one trip from the header (MEASURED; B differs from A by its register allocation and by two UBSan
   pointer-overflow tests, both decided by the engine from the state's facts, so neither adds a case split):
     0x8210c srli a0,s9,3; add a0,a0,s2; lb a0,0(a0); bnez a0 -> 0x82168    (shadow of the text byte; A tests a copy a0)
     0x82168 andi a7,s9,7; bge a7,a0 -> report (dead); j -> 0x8211c         (partial granule, REACHABLE)
     0x8211c lbu a7,1(a3); bltu a4,a7 -> 0x82144                            (c > 32: keep it; a3 = s9 - 1)
     0x82124 srl a0,a6,a7; andi a0,a0,1; beqz a0 -> 0x82140                 (the whitespace bit of c)
     0x82130 addi a3,a3,1; addi s9,s9,1; bne a3,a5 -> 0x8210c               (advance; a5 = -1: UBSan's wrap test,
             (fallthrough 0x8213c j -> 0x82620 unimp: the UBSan trap)        a3 = t + i is never 2^64 - 1)
     0x82140 beqz a7 -> 0x82180                                             (NUL: leave)
     0x82144 bltu a2,a1 -> 0x82620 unimp                                    (UBSan: a2 = ~same, a1 = j; same + j never
                                                                             wraps, so never taken)
     0x82148 add a0,s8,a1; srli t0,a0,3; add t0,t0,s2; lb t0,0(t0); bnez t0 -> 0x82174  (shadow of out[j])
     0x82174 andi t1,a0,7; blt t1,t0 -> 0x8215c; (fallthrough) report (dead)             (partial granule)
     0x8215c addi a1,a1,1; sb a7,0(a0); j -> 0x82130                        (keep: out[j] = c, j := j + 1, advance)
   The two `__asan_report_*` arms are unreachable from the premises: both bytes lie in live blocks, which is what
   the token run's shent_ok says (FSW_K fsw_run_tok_AJU with Bx := fs_Bx, SH := l7_SH; donor A/ACes.v:28-29). The two
   UBSan arms are unreachable from the head state's facts: atom 25 (the cursor) lies in [4096, 2^47 - 2^23] so a3 never
   equals a5 = 2^64 - 1, and atom 12 (a2 = 2^64 - 1 - same) lies above 2^64 - 2^47 while atom 11 (a1 = j) is at most
   3145728 (decide_cond2's interval test, Reusable/YP0e.v:932).
   Register map A -> B at the head: the cursor s9 (25, both; A also a0 = 25), j a2 (12) -> a1 (11), 32 a3 (13) -> a4 (14),
   the mask a4 (14) -> a6 (16), shadow base s2 (18, both); B only: a3 = t + i - 1 (13), a2 = 2^64 - 1 - same (12),
   a5 = 2^64 - 1 (15). The body writes t0 t1 a0 a1 a3 a7 s9 (5 6 10 11 13 17 25; A: 10 11 12 15 16 17 25). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_frame FSW_rres FSW_crt_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec B64Canon.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_crt_base FSH_crt_site.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition L7_HEAD : Z := 0x8210c.
Definition L7_EXIT : Z := 0x82180.
Definition L7_WSMASK : Z := 0x100002600.
(* B only: a5 = -1 (0x820fc `addi a5, zero, -1`), the UBSan wrap test's constant, and the bounds of atom 12 =
   a2 = ~same = 2^64 - 1 - same (0x820f0 `not a2, s8`) for same in [4096, 2^47 - 2^23] *)
Definition L7_M1 : Z := 18446744073709551615.
Definition L7_NLO : Z := 18446603336229584895.
Definition L7_NHI : Z := 18446744073709547519.
Lemma l7_M1_w : Z_to_bv 64 L7_M1 = w64 (2 ^ 64 - 1).
Proof. reflexivity. Qed.

(* ---- the loop head's symbolic state ----
   s9 is atom 25, the text cursor t + i (the shadow check reads s9 itself); a3 is the same atom minus one (the byte read
   is `lbu a7, 1(a3)`); a4 / a6 / a5 are the loop constants the pre-header put there; a2 = ~same keeps its own atom 12
   (with a fact, so the UBSan test 0x82144 `bltu a2, a1` is decided); atom 32 is the shadow base (FSW_K.fs_Bx, the
   lane's atom convention); atom 33 is the text byte under the cursor; atom 34 is s8 + a1, the output cursor, as an
   alias so that the store's address is an atom the token engine can carry. *)
Definition l7_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 13%bv (SOff 25 (-1))) 14%bv (SLit 32)) 15%bv (SLit L7_M1))
    16%bv (SLit L7_WSMASK)) 18%bv (SOff 32 0).
Definition l7_rt : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition l7_ro : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition l7_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 24 0) (SOff 11 0), SOff 34 0); (SAlu ALU_ADD (SOff 11 0) (SOff 24 0), SOff 34 0) ].
Definition l7_facts : facts :=
  mkFacts [ (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 4096 140737479966720 0);
            (24%nat, mkAF 4096 140737479966720 0); (34%nat, mkAF 4096 140737479966720 0);
            (11%nat, mkAF 0 3145728 0); (33%nat, mkAF 0 255 0); (12%nat, mkAF L7_NLO L7_NHI 0) ] [] l7_alias.
Definition l7_ss : sstate := mkSS L7_HEAD l7_regs [l7_rt; l7_ro] None l7_facts.
Definition l7_SH : list shent := [mkSHE 25 0 1; mkSHE 34 0 1].
Definition l7_K : nat := Eval vm_compute in run_K 0 fs_Bx l7_SH l7_ss.
Definition l7_extra (c oc : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 c; Z_to_bv 64 oc].

(* the LAST trip (i = |tb|): the byte under the cursor is the text's NUL, so the state carries it as a literal and
   every branch of the body resolves - one run from the head to the exit, no case split and no output byte *)
Definition l7_rtF : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition l7_factsF : facts :=
  mkFacts [ (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 4096 140737479966720 0);
            (24%nat, mkAF 4096 140737479966720 0); (11%nat, mkAF 0 3145728 0) ] [] [].
Definition l7_ssF : sstate := mkSS L7_HEAD l7_regs [l7_rtF] None l7_factsF.
Definition l7_SHF : list shent := [mkSHE 25 0 1].

(* ---- the plain proof's invariant, on this build's lists (released check_round_trip_loops.v:611-612 cs_pre / cs_j,
   over HState.zs instead of map bv_unsigned) ---- *)
Definition l7_txt (tb : list byte) : list Z := HState.zs (tb ++ [Z_to_bv 8 0]).
Definition l7_byte (tb : list byte) (i : Z) : Z := nth (Z.to_nat i) (l7_txt tb) 0.
Definition l7_pre (tb : list byte) (i : Z) : list Z := b64_strip (firstn (Z.to_nat i) (HState.zs tb)).
Definition l7_j (tb : list byte) (i : Z) : Z := Z.of_nat (length (l7_pre tb i)).

Lemma l7_firstn_snoc : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  intros l. induction l as [|x l IH]; intros n Hn; cbn [length] in Hn; [exfalso; lia|].
  destruct n as [|n]; cbn [firstn nth app]; [reflexivity|]. rewrite IH by (cbn [length] in Hn; lia). reflexivity.
Qed.
Lemma l7_zs_len : forall tb : list byte, length (HState.zs tb) = length tb.
Proof. intros tb. unfold HState.zs. apply length_map. Qed.
Lemma l7_txt_len : forall tb : list byte, Z.of_nat (length (l7_txt tb)) = Z.of_nat (length tb) + 1.
Proof. intros tb. unfold l7_txt, HState.zs. rewrite length_map, length_app. cbn [length]. lia. Qed.
Lemma l7_byte_in : forall tb i, 0 <= i < Z.of_nat (length tb) -> l7_byte tb i = nth (Z.to_nat i) (HState.zs tb) 0.
Proof.
  intros tb i Hi. unfold l7_byte, l7_txt, HState.zs. rewrite map_app. apply app_nth1.
  rewrite length_map. lia.
Qed.
Lemma l7_byte_last : forall tb, l7_byte tb (Z.of_nat (length tb)) = 0.
Proof.
  intros tb. unfold l7_byte, l7_txt, HState.zs. rewrite map_app, Nat2Z.id.
  rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag. reflexivity.
Qed.
Lemma l7_byte_rng : forall tb i, 0 <= l7_byte tb i < 256.
Proof.
  intros tb i. unfold l7_byte, l7_txt, HState.zs.
  destruct (Nat.ltb_spec (Z.to_nat i) (length (map (fun b : byte => bv_unsigned b) (tb ++ [Z_to_bv 8 0])))) as [Hlt|Hge].
  - assert (Hin : In (nth (Z.to_nat i) (map (fun b : byte => bv_unsigned b) (tb ++ [Z_to_bv 8 0])) 0)
                     (map (fun b : byte => bv_unsigned b) (tb ++ [Z_to_bv 8 0]))) by (apply nth_In; exact Hlt).
    apply in_map_iff in Hin as (b & Hb & _). rewrite <- Hb. pose proof (bv_unsigned_in_range 8 b) as H.
    change (bv_modulus 8) with 256 in H. lia.
  - rewrite nth_overflow by exact Hge. lia.
Qed.
Lemma l7_byte_nz : forall tb i, ~ In (Z_to_bv 8 0) tb -> 0 <= i < Z.of_nat (length tb) -> l7_byte tb i <> 0.
Proof.
  intros tb i HNZ Hi E. rewrite (l7_byte_in tb i Hi) in E. apply HNZ.
  unfold HState.zs in E.
  replace 0 with (bv_unsigned (Z_to_bv 8 0)) in E by reflexivity.
  rewrite map_nth in E.
  assert (Hb : nth (Z.to_nat i) tb (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; exact E).
  rewrite <- Hb. apply nth_In. lia.
Qed.
Lemma l7_strip_app : forall l1 l2, b64_strip (l1 ++ l2) = b64_strip l1 ++ b64_strip l2.
Proof. intros l1 l2. unfold b64_strip. apply filter_app. Qed.
Lemma l7_strip_one : forall x, b64_strip [x] = if b64_ws x then [] else [x].
Proof. intros x. rewrite b64_strip_cons. destruct (b64_ws x); reflexivity. Qed.
Lemma l7_pre_step : forall tb i, 0 <= i < Z.of_nat (length tb) ->
  l7_pre tb (i + 1) = l7_pre tb i ++ (if b64_ws (l7_byte tb i) then [] else [l7_byte tb i]).
Proof.
  intros tb i Hi. unfold l7_pre. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite l7_firstn_snoc by (rewrite l7_zs_len; lia).
  rewrite <- (l7_byte_in tb i Hi).
  rewrite l7_strip_app, l7_strip_one. reflexivity.
Qed.
Lemma l7_j_step_keep : forall tb i, 0 <= i < Z.of_nat (length tb) -> b64_ws (l7_byte tb i) = false ->
  l7_j tb (i + 1) = l7_j tb i + 1.
Proof.
  intros tb i Hi HW. unfold l7_j. rewrite (l7_pre_step tb i Hi), HW, length_app. cbn [length]. lia.
Qed.
Lemma l7_j_step_skip : forall tb i, 0 <= i < Z.of_nat (length tb) -> b64_ws (l7_byte tb i) = true ->
  l7_pre tb (i + 1) = l7_pre tb i.
Proof.
  intros tb i Hi HW. rewrite (l7_pre_step tb i Hi), HW. apply app_nil_r.
Qed.
Lemma l7_j_le : forall tb i, 0 <= i -> l7_j tb i <= i.
Proof.
  intros tb i Hi. unfold l7_j, l7_pre.
  assert (H1 : (length (b64_strip (firstn (Z.to_nat i) (HState.zs tb))) <= length (firstn (Z.to_nat i) (HState.zs tb)))%nat)
    by (unfold b64_strip; apply filter_length_le).
  rewrite length_firstn in H1. lia.
Qed.
Lemma l7_j0 : forall tb, l7_pre tb 0 = [] /\ l7_j tb 0 = 0.
Proof. intros tb. unfold l7_j, l7_pre. cbn [Z.to_nat firstn b64_strip filter length]. split; reflexivity. Qed.
(* over 32 is never whitespace; the bit test of 0x100002600 decides it below 32 (released :585 ws_bit, same constant) *)
Lemma l7_ws_big : forall c, 32 < c -> b64_ws c = false.
Proof.
  intros c Hc. unfold b64_ws.
  rewrite (proj2 (Z.eqb_neq c 32)) by lia. rewrite (proj2 (Z.eqb_neq c 9)) by lia.
  rewrite (proj2 (Z.eqb_neq c 10)) by lia. rewrite (proj2 (Z.eqb_neq c 13)) by lia. reflexivity.
Qed.
Lemma l7_ws_bit : forall c, 0 <= c <= 32 ->
  (Z.land (Z.shiftr L7_WSMASK (Z.land c 63)) 1 = 0 <-> b64_ws c = false).
Proof.
  intros c Hc.
  assert (C : forallb (fun n => Bool.eqb (Z.land (Z.shiftr L7_WSMASK (Z.land (Z.of_nat n) 63)) 1 =? 0)
                                         (negb (b64_ws (Z.of_nat n)))) (seq 0 33) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat c) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in C by lia. apply Bool.eqb_prop in C.
  destruct (Z.eqb_spec (Z.land (Z.shiftr L7_WSMASK (Z.land c 63)) 1) 0) as [E|E]; destruct (b64_ws c);
    cbn in C; split; intros; congruence.
Qed.

(* the shifted mask stays inside a word, so the engine's `srl` needs no wrap (used at the bit test) *)
Lemma l7_shiftr_small : forall n, 0 <= n -> 0 <= Z.shiftr L7_WSMASK n <= L7_WSMASK.
Proof.
  intros n Hn. rewrite Z.shiftr_div_pow2 by exact Hn.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as Hp.
  assert (H1 : 1 <= 2 ^ n) by lia.
  split; [apply Z.div_pos; [unfold L7_WSMASK; lia | exact Hp]|].
  apply Z.div_le_upper_bound; [exact Hp|]. unfold L7_WSMASK. nia.
Qed.

(* ---- the three data branches of the body, as closed facts about the byte c under the cursor. Ported from the
   bespoke ASan proof a working branch d25a984c903 lib/A/Prog/check_round_trip_loops.v:717 ws_bit (the same
   constant 4294977024 and the same forallb / vm_compute check over 0 .. 32); restated here on the engine's branch
   condition, so no rewrite ever has to reach inside the run's hypothesis. ---- *)
Lemma l7_bit_val : forall E c, ew E 33 = Z_to_bv 64 c -> 0 <= c < 256 ->
  YP0e.U E (SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff 33 0)) (SLit 1))
    = Z.land (Z.shiftr 4294977024 (Z.land c 63)) 1.
Proof.
  intros E c H Hc.
  pose proof (l7_shiftr_small (Z.land c 63) ltac:(apply Z.land_nonneg; lia)) as HSH.
  unfold L7_WSMASK in HSH.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_lit E 4294977024 ltac:(lia)), (U_lit E 1 ltac:(lia)), (U_atom E 33 c H ltac:(lia)).
  rewrite (zcanon_id (Z.shiftr 4294977024 (Z.land c 63)) ltac:(unfold M64; lia)).
  apply zcanon_id. pose proof (Z_land_upper (Z.shiftr 4294977024 (Z.land c 63)) 1 ltac:(lia)) as HU.
  unfold M64. lia.
Qed.
Lemma l7_bit_eqb : forall E c, ew E 33 = Z_to_bv 64 c -> 0 <= c <= 32 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff 33 0)) (SLit 1)))
    (sv_denot E (SLit 0)) = negb (b64_ws c).
Proof.
  intros E c H Hc.
  rewrite branch_eq_U, (l7_bit_val E c H ltac:(lia)), (U_lit E 0 ltac:(lia)).
  destruct (l7_ws_bit c Hc) as [F1 F2]. unfold L7_WSMASK in F1, F2.
  destruct (Z.eqb_spec (Z.land (Z.shiftr 4294977024 (Z.land c 63)) 1) 0) as [Eq | Ne].
  - rewrite (F1 Eq). reflexivity.
  - assert (WB : b64_ws c = true)
      by (destruct (b64_ws c); [reflexivity | exfalso; exact (Ne (F2 eq_refl))]).
    rewrite WB. reflexivity.
Qed.
Lemma l7_zero_eqb : forall E c, ew E 33 = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff 33 0)) (sv_denot E (SLit 0)) = (c =? 0).
Proof.
  intros E c H Hc. rewrite branch_eq_U, (U_atom E 33 c H ltac:(lia)), (U_lit E 0 ltac:(lia)). reflexivity.
Qed.
Lemma l7_gt32_ltb : forall E c, ew E 33 = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SLit 32)) (sv_denot E (SOff 33 0)) = (32 <? c).
Proof.
  intros E c H Hc. rewrite branch_ltu_U, (U_lit E 32 ltac:(lia)), (U_atom E 33 c H ltac:(lia)). reflexivity.
Qed.

(* the shadow band holds no application byte, so an application byte is never a user-poisoned shadow byte *)
Section Band. Context {rc : YM05.RunCeil}.
Lemma l7_app_not_shadow : forall a, in_app a 1 -> ~ (SHADOW_OFF <= a < kHighMemBeg).
Proof.
  intros a (H1 & [H2 | (H2 & H3)]); unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia.
Qed.
End Band.
Lemma l7_add_atoms : forall E a b x y,
  ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof.
  intros E a b x y Ha Hb H0 H1 H2. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E a x Ha ltac:(lia)), (U_atom E b y Hb ltac:(lia)).
  apply zcanon_id. unfold M64. lia.
Qed.

(* B only: the head's register file against l7_regs (the five pinned registers: a3 = s9 - 1, a4 = 32, a5 = -1,
   a6 = the mask, s2 = the shadow base); every other register is its own atom *)
Lemma l7_regs_ok : forall regs extra c25,
  ew (Ereg regs extra) 32 = Z_to_bv 64 SHADOW_OFF ->
  bv_unsigned (ew (Ereg regs extra) 25) = c25 -> 1 <= c25 < 2 ^ 64 ->
  YK11.getr regs 13%bv = w64 (c25 - 1) -> YK11.getr regs 14%bv = w64 32 ->
  YK11.getr regs 15%bv = w64 (2 ^ 64 - 1) -> YK11.getr regs 16%bv = w64 L7_WSMASK ->
  YK11.getr regs 18%bv = w64 SHADOW_OFF ->
  regs_ok (Ereg regs extra) l7_regs regs.
Proof.
  intros regs extra c25 E32 U25 Hc R13 R14 R15 R16 R18. unfold l7_regs.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
    [apply regs_ok_Ereg | intros X; discriminate X | ] | intros X; discriminate X | ]
    | intros X; discriminate X | ] | intros X; discriminate X | ] | intros X; discriminate X | ].
  - rewrite R13. apply bv_eq. rewrite denot_SOff, U25. rewrite zcanon_id by (unfold M64; lia).
    rewrite unsigned_lit_small by lia. lia.
  - rewrite R14. apply bv_eq.
    change (bv_unsigned (sv_denot (Ereg regs extra) (SLit 32))) with (YP0e.U (Ereg regs extra) (SLit 32)).
    rewrite U_lit by lia. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite R15. apply bv_eq.
    change (bv_unsigned (sv_denot (Ereg regs extra) (SLit L7_M1))) with (YP0e.U (Ereg regs extra) (SLit L7_M1)).
    rewrite U_lit by (unfold L7_M1; lia). rewrite unsigned_lit_small by lia. unfold L7_M1. reflexivity.
  - rewrite R16. apply bv_eq.
    change (bv_unsigned (sv_denot (Ereg regs extra) (SLit L7_WSMASK))) with (YP0e.U (Ereg regs extra) (SLit L7_WSMASK)).
    rewrite U_lit by (unfold L7_WSMASK; lia). rewrite unsigned_lit_small by (unfold L7_WSMASK; lia). reflexivity.
  - rewrite R18, fsw_SOff0. rewrite E32. reflexivity.
Qed.

Section L.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
  (memJ : word -> option byte) (mdJ : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (U : list (Z * Z)) (k : Z) (W : world tfibsegs).
Variables (t same : Z) (tb : list byte) (pt kt ps ks : Z).
(* the text and the output buffer are two live blocks, apart, and the walk may write the output's |tb| + 1 bytes *)
Hypothesis HTBLK : In (pt, kt) (ablocks B lyc Sc).
Hypothesis HTLO : pt <= t.
Hypothesis HTHI : t + Z.of_nat (length tb) + 1 <= pt + req_size kt.
Hypothesis HSBLK : In (ps, ks) (ablocks B lyc Sc).
Hypothesis HSLO : ps <= same.
Hypothesis HSHI : same + Z.of_nat (length tb) + 1 <= ps + req_size ks.
Hypothesis HDJ : same + Z.of_nat (length tb) + 1 <= t \/ t + Z.of_nat (length tb) + 1 <= same.
Hypothesis HWR : forall a, same <= a < same + Z.of_nat (length tb) + 1 ->
  awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a.
Hypothesis HNZ : ~ In (Z_to_bv 8 0) tb.
Hypothesis HLEN : Z.of_nat (length tb) <= 3145728.

(* what the loop knows at the head after i trips: the plain proof's invariant (released :614-618 cs_facts), plus the
   journal and ARU the run step consumes and the nine registers the body reads (B: s9 a3 a1 s8 s2 a4 a6 a2 a5, in
   crt_INV_81fb8's order; A: s9 a0 a2 s8 s2 a3 a4) *)
Definition l7_at (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
  ajournal tfibsegs B STK sp0 FP ly S W0 memJ mdJ own lyc Sc W (unpoison U mem) md k /\
  ARU tfibsegs B lyc Sc U W mem md /\
  zbytes_at tfibsegs W mem t (l7_txt tb) /\
  zbytes_at tfibsegs W mem same (l7_pre tb i) /\
  YK11.getr regs 25%bv = w64 (t + i) /\ YK11.getr regs 13%bv = w64 (t + i - 1) /\
  YK11.getr regs 11%bv = w64 (l7_j tb i) /\ YK11.getr regs 24%bv = w64 same /\
  YK11.getr regs 18%bv = w64 SHADOW_OFF /\ YK11.getr regs 14%bv = w64 32 /\
  YK11.getr regs 16%bv = w64 L7_WSMASK /\ YK11.getr regs 12%bv = w64 (2 ^ 64 - 1 - same) /\
  YK11.getr regs 15%bv = w64 (2 ^ 64 - 1).

(* the two blocks' bounds, on the machine's own memory *)
Lemma l7_blk : forall (mem : word -> option byte) md p n, ARU tfibsegs B lyc Sc U W mem md ->
  In (p, n) (ablocks B lyc Sc) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a).
Proof.
  intros mem md p n HARU Hin.
  pose proof (AR_laws_ok tfibsegs B) as LAWS.
  destruct (al_blocks _ _ LAWS lyc Sc W (unpoison U mem) md p n (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Hin)
    as (_ & H4096 & Hceil & Hia & Hpres & _).
  pose proof (alloc_ceiling_val) as Hac.
  split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hia|].
  intros a Ha. destruct (Hpres a Ha) as (Hp & Hno).
  exact (fsw_apresent_notowned B lyc Sc U W mem md a HARU ltac:(lia) Hno Hp).
Qed.

(* the bounds of the two cursors at trip i *)
Lemma l7_bounds : forall (mem : word -> option byte) md i, ARU tfibsegs B lyc Sc U W mem md ->
  0 <= i <= Z.of_nat (length tb) ->
  4096 <= t /\ t + Z.of_nat (length tb) + 1 <= alloc_ceiling /\ 4096 <= same /\
  same + Z.of_nat (length tb) + 1 <= alloc_ceiling /\ 0 <= l7_j tb i <= i /\
  in_app (t + i) 1 /\ in_app (same + l7_j tb i) 1.
Proof.
  intros mem md i HARU Hi.
  destruct (l7_blk mem md pt kt HARU HTBLK) as (Ht4096 & Htceil & Htia & _).
  destruct (l7_blk mem md ps ks HARU HSBLK) as (Hs4096 & Hsceil & Hsia & _).
  pose proof (l7_j_le tb i ltac:(lia)) as Hjle.
  assert (Hj0 : 0 <= l7_j tb i) by (unfold l7_j; lia).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [eapply in_app_sub; [exact Htia | lia | lia | lia] | eapply in_app_sub; [exact Hsia | lia | lia | lia]].
Qed.

(* the loop head, as the engine reads it: l7_ss over the machine's registers and memory *)
Lemma l7_head_st : forall regs mem md i, 0 <= i <= Z.of_nat (length tb) -> l7_at regs mem md i ->
  st_ok tfibsegs (Ereg regs (l7_extra (l7_byte tb i) (same + l7_j tb i))) l7_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 L7_HEAD) mem (seg_rom tfibsegs))).
Proof.
  intros regs mem md i Hi (HJ & HARU & HTXT & HPRE & R25 & R13 & R11 & R24 & R18 & R14 & R16 & R12 & R15).
  destruct (l7_bounds mem md i HARU Hi) as (Bt1 & Bt2 & Bs1 & Bs2 & Bj & _ & _).
  destruct (l7_blk mem md ps ks HARU HSBLK) as (_ & _ & _ & Hspres).
  destruct (l7_blk mem md pt kt HARU HTBLK) as (_ & _ & _ & _).
  pose proof (l7_byte_rng tb i) as Hc.
  pose proof alloc_ceiling_val as Hac.
  set (c := l7_byte tb i) in *. set (j := l7_j tb i) in *.
  set (E := Ereg regs (l7_extra c (same + j))) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E, l7_extra; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E33 : ew E 33 = Z_to_bv 64 c)
    by (unfold E, l7_extra; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E34 : ew E 34 = Z_to_bv 64 (same + j))
    by (unfold E, l7_extra; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E25 : ew E 25 = Z_to_bv 64 (t + i)) by (unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  assert (E24 : ew E 24 = Z_to_bv 64 same) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E11 : ew E 11 = Z_to_bv 64 j) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
  assert (E12 : ew E 12 = Z_to_bv 64 (2 ^ 64 - 1 - same))
    by (unfold E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
  assert (U25 : bv_unsigned (ew E 25) = t + i) by (rewrite E25; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = same) by (rewrite E24; apply unsigned_lit_small; lia).
  assert (U11 : bv_unsigned (ew E 11) = j) by (rewrite E11; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew E 12) = 2 ^ 64 - 1 - same) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = same + j) by (rewrite E34; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold l7_ss. apply (entry_st_ok_full tfibsegs); try fold E.
  - exact (l7_regs_ok regs _ (t + i) E32 U25 ltac:(lia) R13 R14 R15 R16 R18).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold l7_rt, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (t + i) 0 1 (SOff 33 0) c).
      * rewrite fsw_SOff0. exact E33.
      * cbn [Z.of_N]. change (2 ^ (8 * 1)) with 256. lia.
      * cbn [Z.of_N]. lia.
      * rewrite Z.add_0_r. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        destruct (HTXT (Z.to_nat i) ltac:(unfold l7_txt, HState.zs; rewrite length_map, length_app; cbn [length]; lia))
          as (Hv & _).
        rewrite Z2Nat.id in Hv by lia. exact Hv.
    + unfold l7_ro, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U34. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable tfibsegs). apply Hspres. lia.
  - apply pairwise_disjoint_of_extents. unfold l7_rt, l7_ro, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U25, U34.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; destruct HDJ; first [left; lia | right; lia].
  - split; [|split].
    + unfold l7_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U32, U25, U24, U34, U11, U33, U12. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF, L7_NLO, L7_NHI in *. repeat match goal with |- _ /\ _ => split end; lia.
    + unfold l7_facts. cbn [f_conds conds_ok]. exact I.
    + unfold l7_facts, l7_alias. cbn [f_alias alias_ok]. split; [|split; [|exact I]].
      * rewrite (l7_add_atoms E 24 11 same j E24 E11 ltac:(lia) ltac:(lia) ltac:(lia)).
        rewrite fsw_SOff0, E34. reflexivity.
      * rewrite (l7_add_atoms E 11 24 j same E11 E24 ltac:(lia) ltac:(lia) ltac:(lia)).
        rewrite fsw_SOff0, E34. f_equal. lia.
Qed.

(* ---- the two buffers are outside the user-poisoned heads, so their shadow reads the same on the machine's memory
   as on the allocator's reading (`unpoison U`): this is the U-form of the released contract's "the text lies inside
   an allocator block" premise, in the shape S0 gives the string predicates (cstr_kept takes U). ---- *)
Definition l7_unp (a n : Z) : Prop := Forall (fun r => a + n <= fst r \/ fst r + snd r <= a) U.
Hypothesis HTUP : l7_unp t (Z.of_nat (length tb) + 1).
Hypothesis HSUP : l7_unp same (Z.of_nat (length tb) + 1).

Lemma l7_shadow_same : forall (mem : word -> option byte) md a n, ARU tfibsegs B lyc Sc U W mem md ->
  l7_unp a n -> 0 <= a -> a + n <= alloc_ceiling ->
  forall x, a <= x < a + n ->
  aview tfibsegs (w_H W) (unpoison U mem) (shadow_of_addr SHADOW_OFF x)
    = aview tfibsegs (w_H W) mem (shadow_of_addr SHADOW_OFF x).
Proof.
  intros mem md a n HARU HU Ha Hub x Hx.
  pose proof alloc_ceiling_val as Hac.
  apply aview_unpoison_out.
  destruct (in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)))) eqn:E; [exfalso | reflexivity].
  apply in_ush_spec in E as ((p & len) & Hin & Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
  pose proof (ARU_ok tfibsegs B lyc Sc U W mem md HARU) as (HOK & _).
  destruct (proj1 (Forall_forall _ _) HOK (p, len) Hin) as (Hp8 & Hlen8 & Hlenm & q & m & _ & Hq & Hqm).
  cbn [fst snd] in Hp8, Hlen8, Hlenm, Hq, Hqm.
  assert (Hdiv0 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hdiv : x / 8 <= x) by (apply Z.div_le_upper_bound; lia).
  assert (Hs : bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)) = shadow_of_addr SHADOW_OFF x)
    by (apply unsigned_lit_small; unfold shadow_of_addr, SHADOW_OFF in *; lia).
  rewrite Hs in Hlo, Hhi. unfold shadow_addr, shadow_of_addr in Hlo, Hhi.
  assert (Hpx : p <= x) by (pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.div_mod x 8 ltac:(lia));
    pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
  assert (Hxp : x < p + len)
    by (pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.div_mod x 8 ltac:(lia));
        pose proof (Z.div_mod len 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
  pose proof (proj1 (Forall_forall _ _) HU (p, len) Hin) as [Hd | Hd]; cbn [fst snd] in Hd; lia.
Qed.

(* a sub-range of a live block, outside the poisoned heads, is addressable on the machine's own memory *)
Lemma l7_ra : forall (mem : word -> option byte) md a n p m, ARU tfibsegs B lyc Sc U W mem md ->
  In (p, m) (ablocks B lyc Sc) -> p <= a -> a + n <= p + req_size m -> l7_unp a n -> 0 <= a ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a n.
Proof.
  intros mem md a n p m HARU Hin Hpa Han HU Ha.
  pose proof (AR_laws_ok tfibsegs B) as LAWS.
  destruct (l7_blk mem md p m HARU Hin) as (_ & Hceil & _ & _).
  pose proof (range_addressable_of_block tfibsegs B LAWS lyc Sc W (unpoison U mem) md p m a n
                (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Hin Hpa Han) as RA.
  intros x Hx. destruct (RA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- (l7_shadow_same mem md a n HARU HU Ha ltac:(lia) x Hx). exact Hs.
Qed.

(* the shadow entries of the two cursors, as the token run asks them *)
Lemma l7_sh_ok : forall regs mem md i, 0 <= i <= Z.of_nat (length tb) -> l7_at regs mem md i ->
  sh_ok tfibsegs fs_Bx l7_SH (Ereg regs (l7_extra (l7_byte tb i) (same + l7_j tb i)))
    (mrestrict (w_H W) mem).
Proof.
  intros regs mem md i Hi HAT. pose proof HAT as (_ & HARU & _ & _ & R25 & _ & R11 & R24 & _).
  destruct (l7_bounds mem md i HARU Hi) as (Bt1 & Bt2 & Bs1 & Bs2 & Bj & Ait & Ais).
  pose proof alloc_ceiling_val as Hac.
  set (c := l7_byte tb i) in *. set (j := l7_j tb i) in *.
  set (E := Ereg regs (l7_extra c (same + j))) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E, l7_extra; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E34 : ew E 34 = Z_to_bv 64 (same + j))
    by (unfold E, l7_extra; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E25 : ew E 25 = Z_to_bv 64 (t + i)) by (unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  assert (UB : YP0e.U E fs_Bx = SHADOW_OFF)
    by (unfold fs_Bx; apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
  assert (U25 : YP0e.U E (SOff 25 0) = t + i) by (apply (U_atom E 25 (t + i) E25); lia).
  assert (U34 : YP0e.U E (SOff 34 0) = same + j) by (apply (U_atom E 34 (same + j) E34); lia).
  unfold sh_ok, l7_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 25 t (Z.of_nat (length tb) + 1) (t + i) 0 1).
    + exact (l7_ra mem md t (Z.of_nat (length tb) + 1) pt kt HARU HTBLK HTLO ltac:(lia) HTUP ltac:(lia)).
    + exact UB.
    + exact U25.
    + lia.
    + lia.
    + intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
      apply l7_app_not_shadow. eapply in_app_sub; [exact Ait | lia | lia | lia].
  - apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 34 same (Z.of_nat (length tb) + 1) (same + j) 0 1).
    + exact (l7_ra mem md same (Z.of_nat (length tb) + 1) ps ks HARU HSBLK HSLO ltac:(lia) HSUP ltac:(lia)).
    + exact UB.
    + exact U34.
    + lia.
    + lia.
    + intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
      apply l7_app_not_shadow. eapply in_app_sub; [exact Ais | lia | lia | lia].
Qed.

(* ---- the loop ----
   L7_KEPT: the registers the body leaves alone and whose symbolic value stays their own entry atom; it is the base's
   crt_kept7, as on A. On B, a4 / a5 / a6 / s2 (14 / 15 / 16 / 18) are also untouched but hold constants in the
   state, and a2 (12, ~same) is untouched with its own atom, so l7_at carries all five by value; t0 / t1 / a0 / a1 /
   a3 / a7 / s9 (5 / 6 / 10 / 11 / 13 / 17 / 25) are the body's working set (A: a0 a1 a2 a5 a6 a7 s9); x0 is not in
   the list because its symbolic value is SLit 0, not its own atom (the donor's TIN_KEPT leaves it out for the same
   reason). *)
Definition L7_KEPT : list (bv 5) :=
  [1; 2; 3; 4; 7; 8; 9; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv.
(* what the loop leaves of memory: every byte outside the output buffer *)
Definition l7_mframe (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (same <= a < same + Z.of_nat (length tb) + 1) ->
    m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Lemma l7_mframe_refl : forall m, l7_mframe m m.
Proof. intros m a _ _. reflexivity. Qed.
Lemma l7_mframe_trans : forall m1 m2 m3, l7_mframe m1 m2 -> l7_mframe m2 m3 -> l7_mframe m1 m3.
Proof. intros m1 m2 m3 H1 H2 a Ha Hn. rewrite (H2 a Ha Hn). exact (H1 a Ha Hn). Qed.
(* the run's write window is at most the single output byte under the cursor *)
Definition l7_bframe (w : Z) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> a <> w -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Lemma l7_bframe_of_frame : forall E' (rs : smem) (m m' : word -> option byte) w,
  frame_of E' rs m m' -> (forall a, in_wrange E' rs a -> a = w) -> l7_bframe w m m'.
Proof.
  intros E' rs m m' w HF Hw a Ha Hne. apply HF. intros Hin.
  rewrite unsigned_lit_small in Hin by exact Ha. exact (Hne (Hw a Hin)).
Qed.
Lemma l7_bframe_trans : forall w m1 m2 m3, l7_bframe w m1 m2 -> l7_bframe w m2 m3 -> l7_bframe w m1 m3.
Proof. intros w m1 m2 m3 H1 H2 a Ha Hn. rewrite (H2 a Ha Hn). exact (H1 a Ha Hn). Qed.
Lemma l7_mframe_of_bframe : forall w m m', l7_bframe w m m' ->
  same <= w < same + Z.of_nat (length tb) + 1 -> l7_mframe m m'.
Proof. intros w m m' H Hw a Ha Hn. apply H; [exact Ha | intros ->; exact (Hn Hw)]. Qed.
(* appending the byte just written to the output's prefix *)
Lemma l7_zb_snoc : forall (m : word -> option byte) p l v,
  zbytes_at tfibsegs W m p l -> val_mem tfibsegs (mrestrict (w_H W) m) (p + Z.of_nat (length l)) 1 v ->
  0 <= v < 256 -> zbytes_at tfibsegs W m p (l ++ [v]).
Proof.
  intros m p l v HL HV HR jj Hjj. rewrite length_app in Hjj. cbn [length] in Hjj.
  destruct (Nat.ltb_spec jj (length l)) as [Hlt | Hge].
  - rewrite app_nth1 by exact Hlt. exact (HL jj Hlt).
  - assert (Hj : jj = length l) by lia. subst jj.
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    split; [exact HV | exact HR].
Qed.
(* transporting the invariant's byte arrays across one trip's single store *)
Lemma l7_zb_frame : forall (m m' : word -> option byte) p l w,
  l7_bframe w m m' -> 0 <= p -> p + Z.of_nat (length l) < 2 ^ 64 ->
  ~ (p <= w < p + Z.of_nat (length l)) -> zbytes_at tfibsegs W m p l -> zbytes_at tfibsegs W m' p l.
Proof.
  intros m m' p l w HF Hp Hb Hw HL jj Hjj. destruct (HL jj Hjj) as (HV & HR). split; [|exact HR].
  intros kk Hkk. cbn [Z.of_nat] in Hkk.
  assert (Hk0 : (kk = 0)%nat) by lia. subst kk.
  specialize (HV 0%nat ltac:(cbn; lia)). cbn [Z.of_nat] in HV |- *. rewrite !Z.add_0_r in HV |- *.
  unfold mbyte, mrestrict in HV |- *.
  rewrite (HF (p + Z.of_nat jj) ltac:(lia) ltac:(lia)). exact HV.
Qed.
(* reading a register the run left as an atom, or as an atom plus a literal offset *)
Lemma l7_reg_at : forall (Ex : env) ss ms (r : bv 5) n v,
  st_ok tfibsegs Ex ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  bv_unsigned (ew Ex n) = v -> 0 <= v < 2 ^ 64 -> YK11.getr (ms_regs ms) r = w64 v.
Proof.
  intros Ex ss ms r n v HS Hr Hv Hb. apply bv_eq.
  rewrite (fsw_reg_off (w_H W) Ex ss ms r n 0 v HS Hr Hv ltac:(lia)).
  rewrite unsigned_lit_small by exact Hb. lia.
Qed.
Lemma l7_reg_off : forall (Ex : env) ss ms (r : bv 5) n z v,
  st_ok tfibsegs Ex ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff n z ->
  bv_unsigned (ew Ex n) = v -> 0 <= v + z < 2 ^ 64 -> YK11.getr (ms_regs ms) r = w64 (v + z).
Proof.
  intros Ex ss ms r n z v HS Hr Hv Hb. apply bv_eq.
  rewrite (fsw_reg_off (w_H W) Ex ss ms r n z v HS Hr Hv Hb).
  rewrite unsigned_lit_small by exact Hb. reflexivity.
Qed.

(* ---- re-establishing the invariant at i + 1 from the concrete facts a leaf leaves ---- *)
Lemma l7_keep_done : forall i regs mem md regs2 mem2 md2,
  0 <= i < Z.of_nat (length tb) -> b64_ws (l7_byte tb i) = false -> l7_at regs mem md i ->
  ajournal tfibsegs B STK sp0 FP ly S W0 memJ mdJ own lyc Sc W (unpoison U mem2) md2 k ->
  ARU tfibsegs B lyc Sc U W mem2 md2 ->
  l7_bframe (same + l7_j tb i) mem mem2 ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) (same + l7_j tb i) 1 (l7_byte tb i) ->
  YK11.getr regs2 25%bv = w64 (t + i + 1) -> YK11.getr regs2 13%bv = w64 (t + i) ->
  YK11.getr regs2 11%bv = w64 (l7_j tb i + 1) -> YK11.getr regs2 24%bv = w64 same ->
  YK11.getr regs2 18%bv = w64 SHADOW_OFF -> YK11.getr regs2 14%bv = w64 32 ->
  YK11.getr regs2 16%bv = w64 L7_WSMASK -> YK11.getr regs2 12%bv = w64 (2 ^ 64 - 1 - same) ->
  YK11.getr regs2 15%bv = w64 (2 ^ 64 - 1) ->
  l7_at regs2 mem2 md2 (i + 1).
Proof.
  intros i regs mem md regs2 mem2 md2 Hi HWS HAT HJ2 HARU2 HFR HV Q25 Q13 Q11 Q24 Q18 Q14 Q16 Q12 Q15.
  pose proof HAT as (_ & HARU & HTXT & HPRE & _).
  destruct (l7_bounds mem md i HARU ltac:(lia)) as (Bt1 & Bt2 & Bs1 & Bs2 & Bj & _ & _).
  pose proof alloc_ceiling_val as Hac. pose proof (l7_byte_rng tb i) as Hcr.
  pose proof (l7_txt_len tb) as HTL.
  split; [exact HJ2|]. split; [exact HARU2|]. split.
  - apply (l7_zb_frame mem mem2 t (l7_txt tb) (same + l7_j tb i) HFR ltac:(lia) ltac:(lia)
             ltac:(destruct HDJ; lia) HTXT).
  - split.
    + rewrite (l7_pre_step tb i ltac:(lia)), HWS.
      apply (l7_zb_snoc mem2 same (l7_pre tb i) (l7_byte tb i)); [| exact HV | exact Hcr].
      apply (l7_zb_frame mem mem2 same (l7_pre tb i) (same + l7_j tb i) HFR ltac:(lia)
               ltac:(unfold l7_j in *; lia) ltac:(unfold l7_j in *; lia) HPRE).
    + rewrite (l7_j_step_keep tb i ltac:(lia) HWS).
      replace (t + (i + 1)) with (t + i + 1) by lia. replace (t + i + 1 - 1) with (t + i) by lia.
      split; [exact Q25|]. split; [exact Q13|]. split; [exact Q11|]. split; [exact Q24|].
      split; [exact Q18|]. split; [exact Q14|]. split; [exact Q16|]. split; [exact Q12 | exact Q15].
Qed.
Lemma l7_skip_done : forall i regs mem md regs2 mem2 md2,
  0 <= i < Z.of_nat (length tb) -> b64_ws (l7_byte tb i) = true -> l7_at regs mem md i ->
  ajournal tfibsegs B STK sp0 FP ly S W0 memJ mdJ own lyc Sc W (unpoison U mem2) md2 k ->
  ARU tfibsegs B lyc Sc U W mem2 md2 ->
  l7_bframe (same + l7_j tb i) mem mem2 ->
  YK11.getr regs2 25%bv = w64 (t + i + 1) -> YK11.getr regs2 13%bv = w64 (t + i) ->
  YK11.getr regs2 11%bv = w64 (l7_j tb i) -> YK11.getr regs2 24%bv = w64 same ->
  YK11.getr regs2 18%bv = w64 SHADOW_OFF -> YK11.getr regs2 14%bv = w64 32 ->
  YK11.getr regs2 16%bv = w64 L7_WSMASK -> YK11.getr regs2 12%bv = w64 (2 ^ 64 - 1 - same) ->
  YK11.getr regs2 15%bv = w64 (2 ^ 64 - 1) ->
  l7_at regs2 mem2 md2 (i + 1).
Proof.
  intros i regs mem md regs2 mem2 md2 Hi HWS HAT HJ2 HARU2 HFR Q25 Q13 Q11 Q24 Q18 Q14 Q16 Q12 Q15.
  pose proof HAT as (_ & HARU & HTXT & HPRE & _).
  destruct (l7_bounds mem md i HARU ltac:(lia)) as (Bt1 & Bt2 & Bs1 & Bs2 & Bj & _ & _).
  pose proof alloc_ceiling_val as Hac. pose proof (l7_txt_len tb) as HTL.
  split; [exact HJ2|]. split; [exact HARU2|]. split.
  - apply (l7_zb_frame mem mem2 t (l7_txt tb) (same + l7_j tb i) HFR ltac:(lia) ltac:(lia)
             ltac:(destruct HDJ; lia) HTXT).
  - split.
    + rewrite (l7_j_step_skip tb i ltac:(lia) HWS).
      apply (l7_zb_frame mem mem2 same (l7_pre tb i) (same + l7_j tb i) HFR ltac:(lia)
               ltac:(unfold l7_j in *; lia) ltac:(unfold l7_j in *; lia) HPRE).
    + assert (HJ1 : l7_j tb (i + 1) = l7_j tb i)
        by (unfold l7_j; rewrite (l7_j_step_skip tb i ltac:(lia) HWS); reflexivity).
      rewrite HJ1.
      replace (t + (i + 1)) with (t + i + 1) by lia. replace (t + i + 1 - 1) with (t + i) by lia.
      split; [exact Q25|]. split; [exact Q13|]. split; [exact Q11|]. split; [exact Q24|].
      split; [exact Q18|]. split; [exact Q14|]. split; [exact Q16|]. split; [exact Q12 | exact Q15].
Qed.

(* ---- the two tactics the leaves share ----
   l7_agree: the env after a token run agrees with the one before it below the run's first fresh atom (35: the
   head state's atoms are 0..34); syntactic on purpose, so no conversion between two envs is ever attempted.
   l7_awr: the run's one write window is the output byte under the cursor, which HWR allows. *)
Ltac l7_agree :=
  repeat lazymatch goal with
    | |- YP06.env_agree _ ?X ?X => apply YP06.env_agree_refl
    | |- YP06.env_agree ?kk _ (ewset ?X ?n ?v) =>
        eapply (YP03.env_agree_trans kk _ X);
        [ | apply (YP03.env_agree_le kk n); [lia | apply YP03.env_agree_ewset]]
    | |- YP06.env_agree ?kk _ (havoc ?X ?n ?ws) =>
        eapply (YP03.env_agree_trans kk _ X);
        [ | apply (YP03.env_agree_le kk n); [lia | apply YN3v.env_agree_havoc]]
    end.
Ltac l7_awr U34x AWx :=
  cbn [add_cond ss_mem];
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [l7_rt l7_ro YP09.r_wlo YP09.r_whi]; apply Z.le_refl|]
    | eapply awr_ok_cons_gen;
      [ reflexivity
      | exact U34x
      | let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; cbn [l7_ro YP09.r_wlo YP09.r_whi] in Ha; try rewrite U34x in Ha;
        apply AWx; clear - Ha; lia
      | ] ].

(* the write window of a loop state: its only writable region is the output byte under the cursor *)
Ltac l7_win U34x :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hw := fresh "Hw" in
  intros a (r & Hin & Hw); cbn [add_cond ss_mem l7_ss In] in Hin;
  destruct Hin as [<- | [<- | []]];
  cbn [l7_rt l7_ro YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
  [clear - Hw; lia | rewrite U34x in Hw; clear - Hw; lia].

(* one trip of the loop: from the head at i to the head at i + 1 *)
Lemma l7_iter : forall i regs mem md (Q : world tfibsegs -> config -> Prop),
  0 <= i < Z.of_nat (length tb) -> l7_at regs mem md i ->
  (forall regs' mem' md', l7_at regs' mem' md' (i + 1) ->
     (forall r : bv 5, In r L7_KEPT -> YK11.getr regs' r = YK11.getr regs r) ->
     l7_mframe mem mem' ->
     SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 L7_HEAD) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 L7_HEAD) mem (seg_rom tfibsegs)) md) Q.
Proof.
  intros i regs mem md Q Hi HAT CONT.
  pose proof HAT as (HJ & HARU & HTXT & HPRE & R25 & R13 & R11 & R24 & R18 & R14 & R16 & R12 & R15).
  destruct (l7_bounds mem md i HARU ltac:(lia)) as (Bt1 & Bt2 & Bs1 & Bs2 & Bj & Ait & Ais).
  pose proof alloc_ceiling_val as Hac.
  pose proof (l7_byte_rng tb i) as Hcr.
  pose proof (l7_byte_nz tb i HNZ ltac:(lia)) as Hcnz.
  pose proof (l7_head_st regs mem md i ltac:(lia) HAT) as HS.
  pose proof (l7_sh_ok regs mem md i ltac:(lia) HAT) as SHOK.
  set (c := l7_byte tb i) in *. set (j := l7_j tb i) in *.
  set (E := Ereg regs (l7_extra c (same + j))) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E, l7_extra; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E33 : ew E 33 = Z_to_bv 64 c)
    by (unfold E, l7_extra; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E34 : ew E 34 = Z_to_bv 64 (same + j))
    by (unfold E, l7_extra; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E25 : ew E 25 = Z_to_bv 64 (t + i)) by (unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  assert (E24 : ew E 24 = Z_to_bv 64 same) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E11 : ew E 11 = Z_to_bv 64 j) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
  assert (E12 : ew E 12 = Z_to_bv 64 (2 ^ 64 - 1 - same))
    by (unfold E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
  assert (U34 : bv_unsigned (ew E 34) = same + j) by (rewrite E34; apply unsigned_lit_small; lia).
  (* every arithmetic side condition of the four leaves, derived here while the context is still small: after a
     token run it holds megabyte-sized symbolic states, and `lia` walks all of it *)
  assert (A1 : 0 <= t + i < 2 ^ 64) by (clear - Bt1 Bt2 Hi Hac; lia).
  assert (A2 : 0 <= same < 2 ^ 64) by (clear - Bs1 Bs2 Hac; lia).
  assert (A3 : 0 <= j < 2 ^ 64) by (clear - Bj Hi HLEN Hac; lia).
  assert (A4 : 0 <= SHADOW_OFF < 2 ^ 64) by (clear - Hac; unfold SHADOW_OFF; lia).
  assert (A5 : 0 <= same + j < 2 ^ 64) by (clear - Bs1 Bs2 Bj Hi Hac; lia).
  assert (A6 : 0 <= t + i + 1 < 2 ^ 64) by (clear - Bt1 Bt2 Hi Hac; lia).
  assert (A7 : 0 <= j + 1 < 2 ^ 64) by (clear - Bj Hi HLEN Hac; lia).
  assert (A8 : 0 <= same + 0 < 2 ^ 64) by (clear - Bs1 Bs2 Hac; lia).
  assert (A9 : 0 <= SHADOW_OFF + 0 < 2 ^ 64) by (clear - Hac; unfold SHADOW_OFF; lia).
  assert (A10 : 0 <= 32 < 2 ^ 64) by (clear - Hac; lia).
  assert (A11 : 0 <= L7_WSMASK < 2 ^ 64) by (clear - Hac; unfold L7_WSMASK; lia).
  assert (A12 : 0 <= 2 ^ 64 - 1 - same < 2 ^ 64) by (clear - Bs1 Bs2 Hac; lia).
  assert (A15 : 0 <= L7_M1 < 2 ^ 64) by (clear - Hac; unfold L7_M1; lia).
  assert (AM : same <= same + j < same + Z.of_nat (length tb) + 1) by (clear - Bj Hi; lia).
  assert (AW : forall a, same + j <= a < same + j + 1 ->
           awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a)
    by (intros a Ha; apply HWR; clear - Ha Bj Hi; lia).
  fsw_aj_run_tokU crt_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { l7_awr U34 AW. }
  rename HF into HF1. clear HFr HG.
  lazymatch goal with HS : st_ok _ ?E1 ?S1 (restrict _ ?m1) |- _ =>
    set (Ex := E1) in HS, SHOK; set (Ss1 := S1) in HS; rename m1 into ms1 end.
  assert (AG : YP06.env_agree 35 E Ex) by (unfold Ex; l7_agree).
  assert (F25 : ew Ex 25 = Z_to_bv 64 (t + i)) by (rewrite ((proj1 AG) 25%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E25).
  assert (F24 : ew Ex 24 = Z_to_bv 64 same) by (rewrite ((proj1 AG) 24%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E24).
  assert (F11 : ew Ex 11 = Z_to_bv 64 j) by (rewrite ((proj1 AG) 11%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E11).
  assert (F32 : ew Ex 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite ((proj1 AG) 32%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E32).
  assert (F33 : ew Ex 33 = Z_to_bv 64 c) by (rewrite ((proj1 AG) 33%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E33).
  assert (F34 : ew Ex 34 = Z_to_bv 64 (same + j)) by (rewrite ((proj1 AG) 34%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E34).
  assert (F34u : bv_unsigned (ew Ex 34) = same + j) by (rewrite F34; apply unsigned_lit_small; exact A5).
  srr_branch_tok crt_tbl_ok HS SHOK fs_Bspan.
  - (* 32 <u c: the byte is kept *)
      assert (HWS : b64_ws c = false).
      { pose proof (l7_gt32_ltb Ex c F33 ltac:(clear - Hcr; lia)) as HB. rewrite Hc in HB.
        apply l7_ws_big. symmetry in HB. apply Z.ltb_lt in HB. clear - HB; lia. }
      clear Hc.
    fsw_aj_run_to_tokU crt_tbl_ok HS HJ HARU SHOK fs_Bspan L7_HEAD.
    { l7_awr F34u AW. }
    lazymatch goal with HS : st_ok _ ?EZ ?SZ (restrict _ ?mZ) |- _ =>
      set (Exf := EZ) in HS, SHOK; set (Ssf := SZ) in HS; rename mZ into msf end.
    assert (AGf : YP06.env_agree 35 E Exf) by (unfold Exf, Ex; l7_agree).
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 25%nat ltac:(apply Nat.ltb_lt; reflexivity)))
      (eq_trans (f_equal bv_unsigned E25) (unsigned_lit_small (t + i) A1))) as G25.
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 24%nat ltac:(apply Nat.ltb_lt; reflexivity)))
      (eq_trans (f_equal bv_unsigned E24) (unsigned_lit_small same A2))) as G24.
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 11%nat ltac:(apply Nat.ltb_lt; reflexivity)))
      (eq_trans (f_equal bv_unsigned E11) (unsigned_lit_small j A3))) as G11.
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 12%nat ltac:(apply Nat.ltb_lt; reflexivity)))
      (eq_trans (f_equal bv_unsigned E12) (unsigned_lit_small (2 ^ 64 - 1 - same) A12))) as G12.
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 32%nat ltac:(apply Nat.ltb_lt; reflexivity)))
      (eq_trans (f_equal bv_unsigned E32) (unsigned_lit_small SHADOW_OFF A4))) as G32.
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 34%nat ltac:(apply Nat.ltb_lt; reflexivity)))
      (eq_trans (f_equal bv_unsigned E34) (unsigned_lit_small (same + j) A5))) as G34.
    pose proof (eq_trans (fsw_SOff0 Exf 33) (eq_trans ((proj1 AGf) 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) E33)) as G33.
    assert (VB : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (same + j) 1 c).
    { rewrite <- (Z.add_0_r (same + j)).
      exact (fsw_field Exf (mrestrict (w_H W) (ms_mem msf)) 34 (same + j)
               [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] 0 1 0 1 0 1%N (SOff 33 0) c
               (fsw_region_nth Exf Ssf (restrict (w_H W) msf) 1%nat
                  (YP09.mkRegion (Some 34%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))])
                  HS ltac:(vm_compute; reflexivity))
               G34 ltac:(cbn [In]; left; reflexivity) G33 ltac:(clear - Hcr; cbn [Z.of_N]; lia)
               ltac:(clear - Hac; cbn [Z.of_N]; lia)). }
    assert (RG : forall r : bv 5, In r L7_KEPT -> YK11.getr (ms_regs msf) r = YK11.getr regs r).
    { exact (regs_kept_of_st_ok tfibsegs Exf Ssf (restrict (w_H W) msf) regs (l7_extra c (same + j))
               L7_KEPT HS ltac:(apply (YP03.env_agree_le 32 35); [apply Nat.leb_le; reflexivity | exact AGf])
               ltac:(vm_compute; reflexivity)). }
    assert (HB : l7_bframe (same + j) mem (ms_mem msf)).
    { 
      eapply l7_bframe_trans; [eapply (l7_bframe_of_frame E _ _ _ (same + j) HF1); l7_win U34|].
      eapply (l7_bframe_of_frame Ex _ _ _ (same + j) HF); l7_win F34u. }
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) Exf Ssf msf HS eq_refl).
    apply (CONT (ms_regs msf) (ms_mem msf) _).
    { apply (l7_keep_done i regs mem md (ms_regs msf) (ms_mem msf) _ Hi HWS HAT HJ HARU HB VB).
      - exact (l7_reg_off Exf Ssf msf 25%bv 25 1 (t + i) HS ltac:(vm_compute; reflexivity) G25 A6).
      - exact (l7_reg_at Exf Ssf msf 13%bv 25 (t + i) HS ltac:(vm_compute; reflexivity) G25 A1).
      - exact (l7_reg_off Exf Ssf msf 11%bv 11 1 j HS ltac:(vm_compute; reflexivity) G11 A7).
      - exact (l7_reg_at Exf Ssf msf 24%bv 24 same HS ltac:(vm_compute; reflexivity) G24 A2).
      - exact (l7_reg_at Exf Ssf msf 18%bv 32 SHADOW_OFF HS ltac:(vm_compute; reflexivity) G32 A4).
      - exact (fsw_reg_lit (w_H W) Exf Ssf msf 14%bv 32 HS ltac:(vm_compute; reflexivity) A10).
      - exact (fsw_reg_lit (w_H W) Exf Ssf msf 16%bv L7_WSMASK HS ltac:(vm_compute; reflexivity) A11).
      - exact (l7_reg_at Exf Ssf msf 12%bv 12 (2 ^ 64 - 1 - same) HS ltac:(vm_compute; reflexivity) G12 A12).
      - exact (eq_trans (fsw_reg_lit (w_H W) Exf Ssf msf 15%bv L7_M1 HS ltac:(vm_compute; reflexivity) A15) l7_M1_w). }
    { exact RG. }
    { exact (l7_mframe_of_bframe (same + j) mem (ms_mem msf) HB AM). }
  - (* c <= 32: the whitespace bit of 0x100002600 decides *)
    assert (HC32 : c <= 32).
    { pose proof (l7_gt32_ltb Ex c F33 ltac:(clear - Hcr; lia)) as HB. rewrite Hc in HB.
      symmetry in HB. apply Z.ltb_ge in HB. clear - HB; lia. }
    clear Hc.
    fsw_aj_run_tokU crt_tbl_ok HS HJ HARU SHOK fs_Bspan.
    { l7_awr F34u AW. }
    rename HF into HF2. clear HFr HG.
    lazymatch goal with HS : st_ok _ ?E3 ?S3 (restrict _ ?m3) |- _ =>
      set (Ex3 := E3) in HS, SHOK; set (Ss3 := S3) in HS; rename m3 into ms3 end.
    assert (AG3 : YP06.env_agree 35 E Ex3) by (unfold Ex3, Ex; l7_agree).
    assert (F25b : ew Ex3 25 = Z_to_bv 64 (t + i)) by (rewrite ((proj1 AG3) 25%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E25).
    assert (F24b : ew Ex3 24 = Z_to_bv 64 same) by (rewrite ((proj1 AG3) 24%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E24).
    assert (F11b : ew Ex3 11 = Z_to_bv 64 j) by (rewrite ((proj1 AG3) 11%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E11).
    assert (F32b : ew Ex3 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite ((proj1 AG3) 32%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E32).
    assert (F33b : ew Ex3 33 = Z_to_bv 64 c) by (rewrite ((proj1 AG3) 33%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E33).
    assert (F34b : ew Ex3 34 = Z_to_bv 64 (same + j)) by (rewrite ((proj1 AG3) 34%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E34).
    assert (F34ub : bv_unsigned (ew Ex3 34) = same + j) by (rewrite F34b; apply unsigned_lit_small; exact A5).
    srr_branch_tok crt_tbl_ok HS SHOK fs_Bspan.
    + (* the bit is 0: the byte is not whitespace *)
      assert (HWS : b64_ws c = false).
      { pose proof (l7_bit_eqb Ex3 c F33b ltac:(clear - Hcr HC32; lia)) as HB. rewrite Hc in HB.
        symmetry in HB. apply negb_true_iff in HB. exact HB. }
      clear Hc.
      fsw_aj_run_tokU crt_tbl_ok HS HJ HARU SHOK fs_Bspan.
      { l7_awr F34ub AW. }
      rename HF into HF3. clear HFr HG.
      lazymatch goal with HS : st_ok _ ?E5 ?S5 (restrict _ ?m5) |- _ =>
        set (Ex5 := E5) in HS, SHOK; set (Ss5 := S5) in HS; rename m5 into ms5 end.
      assert (AG5 : YP06.env_agree 35 E Ex5) by (unfold Ex5, Ex3, Ex; l7_agree).
      assert (F25d : ew Ex5 25 = Z_to_bv 64 (t + i)) by (rewrite ((proj1 AG5) 25%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E25).
      assert (F24d : ew Ex5 24 = Z_to_bv 64 same) by (rewrite ((proj1 AG5) 24%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E24).
      assert (F11d : ew Ex5 11 = Z_to_bv 64 j) by (rewrite ((proj1 AG5) 11%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E11).
      assert (F32d : ew Ex5 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite ((proj1 AG5) 32%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E32).
      assert (F33d : ew Ex5 33 = Z_to_bv 64 c) by (rewrite ((proj1 AG5) 33%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E33).
      assert (F34d : ew Ex5 34 = Z_to_bv 64 (same + j)) by (rewrite ((proj1 AG5) 34%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact E34).
      assert (F34ud : bv_unsigned (ew Ex5 34) = same + j) by (rewrite F34d; apply unsigned_lit_small; exact A5).
      srr_branch_tok crt_tbl_ok HS SHOK fs_Bspan.
      * (* c = 0 cannot happen inside the text: the NUL is only at t + |tb| *)
        exfalso. pose proof (l7_zero_eqb Ex5 c F33d ltac:(clear - Hcr; lia)) as HB. rewrite Hc in HB.
        symmetry in HB. apply Z.eqb_eq in HB. exact (Hcnz HB).
      * clear Hc.
        fsw_aj_run_to_tokU crt_tbl_ok HS HJ HARU SHOK fs_Bspan L7_HEAD.
        { l7_awr F34ud AW. }
        lazymatch goal with HS : st_ok _ ?EZ ?SZ (restrict _ ?mZ) |- _ =>
          set (Exf := EZ) in HS, SHOK; set (Ssf := SZ) in HS; rename mZ into msf end.
        assert (AGf : YP06.env_agree 35 E Exf) by (unfold Exf, Ex5, Ex3, Ex; l7_agree).
        pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 25%nat ltac:(apply Nat.ltb_lt; reflexivity)))
          (eq_trans (f_equal bv_unsigned E25) (unsigned_lit_small (t + i) A1))) as G25.
        pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 24%nat ltac:(apply Nat.ltb_lt; reflexivity)))
          (eq_trans (f_equal bv_unsigned E24) (unsigned_lit_small same A2))) as G24.
        pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 11%nat ltac:(apply Nat.ltb_lt; reflexivity)))
          (eq_trans (f_equal bv_unsigned E11) (unsigned_lit_small j A3))) as G11.
        pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 12%nat ltac:(apply Nat.ltb_lt; reflexivity)))
          (eq_trans (f_equal bv_unsigned E12) (unsigned_lit_small (2 ^ 64 - 1 - same) A12))) as G12.
        pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 32%nat ltac:(apply Nat.ltb_lt; reflexivity)))
          (eq_trans (f_equal bv_unsigned E32) (unsigned_lit_small SHADOW_OFF A4))) as G32.
        pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 34%nat ltac:(apply Nat.ltb_lt; reflexivity)))
          (eq_trans (f_equal bv_unsigned E34) (unsigned_lit_small (same + j) A5))) as G34.
        pose proof (eq_trans (fsw_SOff0 Exf 33) (eq_trans ((proj1 AGf) 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) E33)) as G33.
        assert (VB : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msf)) (same + j) 1 c).
        { rewrite <- (Z.add_0_r (same + j)).
          exact (fsw_field Exf (mrestrict (w_H W) (ms_mem msf)) 34 (same + j)
                   [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] 0 1 0 1 0 1%N (SOff 33 0) c
                   (fsw_region_nth Exf Ssf (restrict (w_H W) msf) 1%nat
                      (YP09.mkRegion (Some 34%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))])
                      HS ltac:(vm_compute; reflexivity))
                   G34 ltac:(cbn [In]; left; reflexivity) G33 ltac:(clear - Hcr; cbn [Z.of_N]; lia)
                   ltac:(clear - Hac; cbn [Z.of_N]; lia)). }
        assert (RG : forall r : bv 5, In r L7_KEPT -> YK11.getr (ms_regs msf) r = YK11.getr regs r).
        { exact (regs_kept_of_st_ok tfibsegs Exf Ssf (restrict (w_H W) msf) regs (l7_extra c (same + j))
                   L7_KEPT HS ltac:(apply (YP03.env_agree_le 32 35); [apply Nat.leb_le; reflexivity | exact AGf])
                   ltac:(vm_compute; reflexivity)). }
        assert (HB : l7_bframe (same + j) mem (ms_mem msf)).
        { 
          eapply l7_bframe_trans; [eapply (l7_bframe_of_frame E _ _ _ (same + j) HF1); l7_win U34|].
          eapply l7_bframe_trans; [eapply (l7_bframe_of_frame Ex _ _ _ (same + j) HF2); l7_win F34u|].
          eapply l7_bframe_trans; [eapply (l7_bframe_of_frame Ex3 _ _ _ (same + j) HF3); l7_win F34ub|].
          eapply (l7_bframe_of_frame Ex5 _ _ _ (same + j) HF); l7_win F34ud. }
        rewrite (st_ok_restrict_mkst tfibsegs (w_H W) Exf Ssf msf HS eq_refl).
        apply (CONT (ms_regs msf) (ms_mem msf) _).
        { apply (l7_keep_done i regs mem md (ms_regs msf) (ms_mem msf) _ Hi HWS HAT HJ HARU HB VB).
          - exact (l7_reg_off Exf Ssf msf 25%bv 25 1 (t + i) HS ltac:(vm_compute; reflexivity) G25 A6).
          - exact (l7_reg_at Exf Ssf msf 13%bv 25 (t + i) HS ltac:(vm_compute; reflexivity) G25 A1).
          - exact (l7_reg_off Exf Ssf msf 11%bv 11 1 j HS ltac:(vm_compute; reflexivity) G11 A7).
          - exact (l7_reg_at Exf Ssf msf 24%bv 24 same HS ltac:(vm_compute; reflexivity) G24 A2).
          - exact (l7_reg_at Exf Ssf msf 18%bv 32 SHADOW_OFF HS ltac:(vm_compute; reflexivity) G32 A4).
          - exact (fsw_reg_lit (w_H W) Exf Ssf msf 14%bv 32 HS ltac:(vm_compute; reflexivity) A10).
          - exact (fsw_reg_lit (w_H W) Exf Ssf msf 16%bv L7_WSMASK HS ltac:(vm_compute; reflexivity) A11).
          - exact (l7_reg_at Exf Ssf msf 12%bv 12 (2 ^ 64 - 1 - same) HS ltac:(vm_compute; reflexivity) G12 A12).
          - exact (eq_trans (fsw_reg_lit (w_H W) Exf Ssf msf 15%bv L7_M1 HS ltac:(vm_compute; reflexivity) A15) l7_M1_w). }
        { exact RG. }
        { exact (l7_mframe_of_bframe (same + j) mem (ms_mem msf) HB AM). }
    + (* the bit is 1: the byte is whitespace and is skipped *)
      assert (HWS : b64_ws c = true).
      { pose proof (l7_bit_eqb Ex3 c F33b ltac:(clear - Hcr HC32; lia)) as HB. rewrite Hc in HB.
        symmetry in HB. apply negb_false_iff in HB. exact HB. }
      clear Hc.
      fsw_aj_run_to_tokU crt_tbl_ok HS HJ HARU SHOK fs_Bspan L7_HEAD.
      { l7_awr F34ub AW. }
      lazymatch goal with HS : st_ok _ ?EZ ?SZ (restrict _ ?mZ) |- _ =>
        set (Exf := EZ) in HS, SHOK; set (Ssf := SZ) in HS; rename mZ into msf end.
      assert (AGf : YP06.env_agree 35 E Exf) by (unfold Exf, Ex3, Ex; l7_agree).
      pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 25%nat ltac:(apply Nat.ltb_lt; reflexivity)))
        (eq_trans (f_equal bv_unsigned E25) (unsigned_lit_small (t + i) A1))) as G25.
      pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 24%nat ltac:(apply Nat.ltb_lt; reflexivity)))
        (eq_trans (f_equal bv_unsigned E24) (unsigned_lit_small same A2))) as G24.
      pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 11%nat ltac:(apply Nat.ltb_lt; reflexivity)))
        (eq_trans (f_equal bv_unsigned E11) (unsigned_lit_small j A3))) as G11.
      pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 12%nat ltac:(apply Nat.ltb_lt; reflexivity)))
        (eq_trans (f_equal bv_unsigned E12) (unsigned_lit_small (2 ^ 64 - 1 - same) A12))) as G12.
      pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 32%nat ltac:(apply Nat.ltb_lt; reflexivity)))
        (eq_trans (f_equal bv_unsigned E32) (unsigned_lit_small SHADOW_OFF A4))) as G32.
      pose proof (eq_trans (f_equal bv_unsigned ((proj1 AGf) 34%nat ltac:(apply Nat.ltb_lt; reflexivity)))
        (eq_trans (f_equal bv_unsigned E34) (unsigned_lit_small (same + j) A5))) as G34.
      pose proof (eq_trans (fsw_SOff0 Exf 33) (eq_trans ((proj1 AGf) 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) E33)) as G33.
      assert (RG : forall r : bv 5, In r L7_KEPT -> YK11.getr (ms_regs msf) r = YK11.getr regs r).
      { exact (regs_kept_of_st_ok tfibsegs Exf Ssf (restrict (w_H W) msf) regs (l7_extra c (same + j))
                 L7_KEPT HS ltac:(apply (YP03.env_agree_le 32 35); [apply Nat.leb_le; reflexivity | exact AGf])
                 ltac:(vm_compute; reflexivity)). }
      assert (HB : l7_bframe (same + j) mem (ms_mem msf)).
      { 
        eapply l7_bframe_trans; [eapply (l7_bframe_of_frame E _ _ _ (same + j) HF1); l7_win U34|].
        eapply l7_bframe_trans; [eapply (l7_bframe_of_frame Ex _ _ _ (same + j) HF2); l7_win F34u|].
        eapply (l7_bframe_of_frame Ex3 _ _ _ (same + j) HF); l7_win F34ub. }
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) Exf Ssf msf HS eq_refl).
      apply (CONT (ms_regs msf) (ms_mem msf) _).
      { apply (l7_skip_done i regs mem md (ms_regs msf) (ms_mem msf) _ Hi HWS HAT HJ HARU HB).
        - exact (l7_reg_off Exf Ssf msf 25%bv 25 1 (t + i) HS ltac:(vm_compute; reflexivity) G25 A6).
        - exact (l7_reg_at Exf Ssf msf 13%bv 25 (t + i) HS ltac:(vm_compute; reflexivity) G25 A1).
        - exact (l7_reg_at Exf Ssf msf 11%bv 11 j HS ltac:(vm_compute; reflexivity) G11 A3).
        - exact (l7_reg_at Exf Ssf msf 24%bv 24 same HS ltac:(vm_compute; reflexivity) G24 A2).
        - exact (l7_reg_at Exf Ssf msf 18%bv 32 SHADOW_OFF HS ltac:(vm_compute; reflexivity) G32 A4).
        - exact (fsw_reg_lit (w_H W) Exf Ssf msf 14%bv 32 HS ltac:(vm_compute; reflexivity) A10).
        - exact (fsw_reg_lit (w_H W) Exf Ssf msf 16%bv L7_WSMASK HS ltac:(vm_compute; reflexivity) A11).
        - exact (l7_reg_at Exf Ssf msf 12%bv 12 (2 ^ 64 - 1 - same) HS ltac:(vm_compute; reflexivity) G12 A12).
        - exact (eq_trans (fsw_reg_lit (w_H W) Exf Ssf msf 15%bv L7_M1 HS ltac:(vm_compute; reflexivity) A15) l7_M1_w). }
      { exact RG. }
      { exact (l7_mframe_of_bframe (same + j) mem (ms_mem msf) HB AM). }
Qed.

(* the last trip: the NUL under the cursor, straight to the exit *)
Lemma l7_fin : forall regs mem md (Q : world tfibsegs -> config -> Prop),
  l7_at regs mem md (Z.of_nat (length tb)) ->
  (forall regs' mem' md', l7_at regs' mem' md' (Z.of_nat (length tb)) ->
     (forall r : bv 5, In r L7_KEPT -> YK11.getr regs' r = YK11.getr regs r) ->
     l7_mframe mem mem' ->
     SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 L7_EXIT) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 L7_HEAD) mem (seg_rom tfibsegs)) md) Q.
Proof.
  intros regs mem md Q HAT CONT.
  pose proof HAT as (HJ & HARU & HTXT & HPRE & R25 & R13 & R11 & R24 & R18 & R14 & R16 & R12 & R15).
  set (N := Z.of_nat (length tb)) in *.
  destruct (l7_bounds mem md N HARU ltac:(lia)) as (Bt1 & Bt2 & Bs1 & Bs2 & Bj & Ait & Ais).
  pose proof alloc_ceiling_val as Hac. pose proof (l7_txt_len tb) as HTL.
  set (j := l7_j tb N) in *.
  set (E := Ereg regs (l7_extra 0 (same + j))) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E, l7_extra; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E25 : ew E 25 = Z_to_bv 64 (t + N)) by (unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  assert (E24 : ew E 24 = Z_to_bv 64 same) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E11 : ew E 11 = Z_to_bv 64 j) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
  assert (E12 : ew E 12 = Z_to_bv 64 (2 ^ 64 - 1 - same))
    by (unfold E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
  assert (U25 : bv_unsigned (ew E 25) = t + N) by (rewrite E25; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = same) by (rewrite E24; apply unsigned_lit_small; lia).
  assert (U11 : bv_unsigned (ew E 11) = j) by (rewrite E11; apply unsigned_lit_small; unfold l7_j in *; lia).
  assert (U12 : bv_unsigned (ew E 12) = 2 ^ 64 - 1 - same) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF)
    by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  (* the leaf's arithmetic side conditions, derived while the context is still small (see l7_iter) *)
  assert (A1 : 0 <= t + N < 2 ^ 64) by (clear - Bt1 Bt2 Hac; unfold N; lia).
  assert (A2s : 0 <= same < 2 ^ 64) by (clear - Bs1 Bs2 Hac; lia).
  assert (A4s : 0 <= SHADOW_OFF < 2 ^ 64) by (clear - Hac; unfold SHADOW_OFF; lia).
  assert (A3 : 0 <= j < 2 ^ 64) by (clear - Bj Hac HLEN; unfold N in *; lia).
  assert (A9 : 0 <= SHADOW_OFF + 0 < 2 ^ 64) by (clear - Hac; unfold SHADOW_OFF; lia).
  assert (A10 : 0 <= 32 < 2 ^ 64) by (clear - Hac; lia).
  assert (A11 : 0 <= L7_WSMASK < 2 ^ 64) by (clear - Hac; unfold L7_WSMASK; lia).
  assert (A12 : 0 <= 2 ^ 64 - 1 - same < 2 ^ 64) by (clear - Bs1 Bs2 Hac; lia).
  assert (A13 : 0 <= t + N + -1 < 2 ^ 64) by (clear - Bt1 Bt2 Hac; unfold N; lia).
  assert (A15 : 0 <= L7_M1 < 2 ^ 64) by (clear - Hac; unfold L7_M1; lia).
  assert (AT1 : 0 <= t) by (clear - Bt1; lia).
  assert (AT2 : t + Z.of_nat (length (l7_txt tb)) < 2 ^ 64) by (clear - Bt1 Bt2 Hac HTL; lia).
  assert (AT3 : ~ (t <= same + j < t + Z.of_nat (length (l7_txt tb))))
    by (clear - HDJ Bj HTL Bt1 Bs1; unfold N in *; lia).
  assert (AS1 : 0 <= same) by (clear - Bs1; lia).
  assert (AS2 : same + Z.of_nat (length (l7_pre tb N)) < 2 ^ 64) by (clear - Bs1 Bs2 Bj Hac; unfold j, l7_j in *; lia).
  assert (AS3 : ~ (same <= same + j < same + Z.of_nat (length (l7_pre tb N))))
    by (clear - Bj; unfold j, l7_j in *; lia).
  (* the head state: the byte under the cursor is the text's NUL, so it is a literal and no branch is left open *)
  assert (HS : st_ok tfibsegs E l7_ssF (restrict (w_H W) (mkst regs (Z_to_bv 64 L7_HEAD) mem (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold l7_ssF. apply (entry_st_ok_full tfibsegs); try fold E.
    - exact (l7_regs_ok regs _ (t + N) E32 U25 ltac:(clear - Bt1 Bt2 Hac; unfold N; lia) R13 R14 R15 R16 R18).
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold l7_rtF, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (t + N) 0 1 (SLit 0) 0).
      + apply bv_eq. change (bv_unsigned (sv_denot E (SLit 0))) with (YP0e.U E (SLit 0)).
        rewrite U_lit by lia. rewrite unsigned_lit_small by lia. reflexivity.
      + cbn [Z.of_N]. lia.
      + cbn [Z.of_N]. lia.
      + rewrite Z.add_0_r. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        destruct (HTXT (Z.to_nat N) ltac:(unfold l7_txt, HState.zs; rewrite length_map, length_app;
                                          cbn [length]; unfold N; lia)) as (Hv & _).
        rewrite Z2Nat.id in Hv by lia. rewrite <- (l7_byte_last tb). exact Hv.
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - split; [|split].
      + unfold l7_factsF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U32, U25, U24, U11. rewrite !Z.pow_0_r, !Z.mod_1_r.
        unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; unfold l7_j in *; lia.
      + unfold l7_factsF. cbn [f_conds conds_ok]. exact I.
      + unfold l7_factsF. cbn [f_alias alias_ok]. exact I. }
  assert (SHOK : sh_ok tfibsegs fs_Bx l7_SHF E (mrestrict (w_H W) mem)).
  { unfold sh_ok, l7_SHF. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 25 t (Z.of_nat (length tb) + 1) (t + N) 0 1).
    - exact (l7_ra mem md t (Z.of_nat (length tb) + 1) pt kt HARU HTBLK HTLO ltac:(lia) HTUP ltac:(lia)).
    - unfold fs_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
    - apply (U_atom E 25 (t + N) E25). lia.
    - lia.
    - lia.
    - intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
      apply l7_app_not_shadow. eapply in_app_sub; [exact Ait | lia | lia | lia]. }
  fsw_aj_run_to_tokU crt_tbl_ok HS HJ HARU SHOK fs_Bspan L7_EXIT.
  { apply awr_ok_cons_ro; [cbn [l7_rtF YP09.r_wlo YP09.r_whi]; apply Z.le_refl|]. apply awr_ok_nil. }
  lazymatch goal with
  | HS : st_ok _ ?Ex2 ?ss2 (restrict _ ?ms2) |- _ =>
    (* the last-trip state l7_ssF has atoms 0 .. 32 only (the NUL is a literal, no output cursor), so the run's first
       fresh atom is 33 *)
    assert (AG2 : YP06.env_agree 33 E Ex2) by l7_agree;
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AG2) 25%nat ltac:(apply Nat.ltb_lt; reflexivity))) U25) as G25;
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AG2) 24%nat ltac:(apply Nat.ltb_lt; reflexivity))) U24) as G24;
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AG2) 11%nat ltac:(apply Nat.ltb_lt; reflexivity))) U11) as G11;
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AG2) 12%nat ltac:(apply Nat.ltb_lt; reflexivity))) U12) as G12;
    pose proof (eq_trans (f_equal bv_unsigned ((proj1 AG2) 32%nat ltac:(apply Nat.ltb_lt; reflexivity))) U32) as G32;
    assert (HB : forall a, 0 <= a < 2 ^ 64 -> ms_mem ms2 (Z_to_bv 64 a) = mem (Z_to_bv 64 a))
      by (intros a Ha; apply HF; intros (r & Hin & Hw); cbn [l7_ssF ss_mem In] in Hin;
          destruct Hin as [<- | []]; cbn [l7_rtF YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; clear - Hw; lia);
    assert (HBF : l7_bframe (same + j) mem (ms_mem ms2)) by (intros a Ha _; exact (HB a Ha));
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) Ex2 ss2 ms2 HS eq_refl);
    apply (CONT (ms_regs ms2) (ms_mem ms2) _);
    [ split; [exact HJ|]; split; [exact HARU|]; split;
      [ apply (l7_zb_frame mem (ms_mem ms2) t (l7_txt tb) (same + j) HBF AT1 AT2 AT3 HTXT) |];
      split;
      [ apply (l7_zb_frame mem (ms_mem ms2) same (l7_pre tb N) (same + j) HBF AS1 AS2 AS3 HPRE) |];
      split; [exact (l7_reg_at Ex2 ss2 ms2 25%bv 25 (t + N) HS ltac:(vm_compute; reflexivity) G25 A1)|];
      split; [rewrite (l7_reg_off Ex2 ss2 ms2 13%bv 25 (-1) (t + N) HS ltac:(vm_compute; reflexivity) G25 A13);
              f_equal; ring|];
      split; [exact (l7_reg_at Ex2 ss2 ms2 11%bv 11 j HS ltac:(vm_compute; reflexivity) G11 A3)|];
      split; [exact (l7_reg_at Ex2 ss2 ms2 24%bv 24 same HS ltac:(vm_compute; reflexivity) G24 A2s)|];
      split; [exact (l7_reg_at Ex2 ss2 ms2 18%bv 32 SHADOW_OFF HS ltac:(vm_compute; reflexivity) G32 A4s)|];
      split; [exact (fsw_reg_lit (w_H W) Ex2 ss2 ms2 14%bv 32 HS ltac:(vm_compute; reflexivity) A10)|];
      split; [exact (fsw_reg_lit (w_H W) Ex2 ss2 ms2 16%bv L7_WSMASK HS ltac:(vm_compute; reflexivity) A11)|];
      split; [exact (l7_reg_at Ex2 ss2 ms2 12%bv 12 (2 ^ 64 - 1 - same) HS ltac:(vm_compute; reflexivity) G12 A12)
             | exact (eq_trans (fsw_reg_lit (w_H W) Ex2 ss2 ms2 15%bv L7_M1 HS ltac:(vm_compute; reflexivity) A15) l7_M1_w)]
    | apply (regs_kept_of_st_ok tfibsegs Ex2 ss2 (restrict (w_H W) ms2) regs (l7_extra 0 (same + j)) L7_KEPT HS
               ltac:(apply (YP03.env_agree_le 32 33); [apply Nat.leb_le; reflexivity | exact AG2]) ltac:(vm_compute; reflexivity))
    | intros a Ha _; exact (HB a Ha) ]
  end.
Qed.

(* the whole loop, by induction on the trips left (released check_round_trip_loops.v:768 cs_loop) *)
Lemma l7_loop : forall (n : nat) (i : Z) regs mem md (Q : world tfibsegs -> config -> Prop),
  Z.to_nat (Z.of_nat (length tb) - i) = n -> 0 <= i <= Z.of_nat (length tb) ->
  l7_at regs mem md i ->
  (forall regs' mem' md', l7_at regs' mem' md' (Z.of_nat (length tb)) ->
     (forall r : bv 5, In r L7_KEPT -> YK11.getr regs' r = YK11.getr regs r) ->
     l7_mframe mem mem' ->
     SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 L7_EXIT) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 L7_HEAD) mem (seg_rom tfibsegs)) md) Q.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros i regs mem md Q Hn Hi HAT CONT.
  destruct (Z.eq_dec i (Z.of_nat (length tb))) as [Heq | Hne].
  - rewrite Heq in HAT. exact (l7_fin regs mem md Q HAT CONT).
  - apply (l7_iter i regs mem md Q ltac:(lia) HAT).
    intros regs1 mem1 md1 HAT1 HK1 HF1.
    apply (IH (Z.to_nat (Z.of_nat (length tb) - (i + 1))) ltac:(lia) (i + 1) regs1 mem1 md1 Q eq_refl ltac:(lia) HAT1).
    intros regs' mem' md' HAT' HK' HF'.
    apply CONT; [exact HAT' | | exact (l7_mframe_trans mem mem1 mem' HF1 HF')].
    intros r Hr. rewrite (HK' r Hr). exact (HK1 r Hr).
Qed.

(* ---- the loop lemma of segment 7, as a Theorem Labs lane's seg-7 step consumes it: from the head 0x8210c (A 0x81fb8) with an
   empty output to the exit 0x82180 (A 0x82028) with `canonical`'s answer in it. Q is free, so it composes with FSH_crt_base's crt_from:
   `crt_from ss_exit INV_exit -> crt_from ss_head INV_head` is this lemma at Q := crt_post cx. ---- *)
Theorem crt_l7 : forall regs mem md (Q : world tfibsegs -> config -> Prop),
  l7_at regs mem md 0 ->
  (forall regs' mem' md', l7_at regs' mem' md' (Z.of_nat (length tb)) ->
     (forall r : bv 5, In r L7_KEPT -> YK11.getr regs' r = YK11.getr regs r) ->
     l7_mframe mem mem' ->
     SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 L7_EXIT) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 L7_HEAD) mem (seg_rom tfibsegs)) md) Q.
Proof.
  intros regs mem md Q HAT CONT.
  exact (l7_loop (Z.to_nat (Z.of_nat (length tb) - 0)) 0 regs mem md Q eq_refl
           ltac:(pose proof (Zle_0_nat (length tb)); lia) HAT CONT).
Qed.
End L.

(* ================================================================================================================
   LANE L7's SEGMENT LEMMA: crt_INV_81fb8 -> crt_INV_82028, frame-generic in R (the walk's design, a Theorem Labs lane 05:2xZ).
   The boundary states are the ones a Theorem Labs lane agreed: crt_ss_ret L7_HEAD / L7_EXIT crt_cs1 crt_csF (B 0x8210c /
   0x82180; B's crt_cs1 holds every slot from 0x820e8 on), all registers
   atoms. The loop writes only the output buffer, so each of the four boundary regions - the s0 words and the s1
   slots (stack, above alloc_ceiling), the class-3 frame and its shadow - is carried across byte for byte.
   ================================================================================================================ *)
Section Seg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the atoms the four boundary regions and the boundary facts read: the two stack bases, the frame's shadow base (B:
   s10 = atom 26; A: s3 = atom 19), and crt_extra's nineteen (B adds atom 50 = En) *)
Definition l7_PA (n : nat) : bool :=
  Nat.eqb n 8 || Nat.eqb n 9 || Nat.eqb n 26 || ((32 <=? n) && (n <? 32 + crt_nextra))%nat.

(* a byte outside the loop's write window reads the same before and after *)
Lemma l7_keep_byte : forall (W3 : world tfibsegs) (m m' : word -> option byte) (lo hi a : Z),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  mbyte tfibsegs (mrestrict (w_H W3) m') a = mbyte tfibsegs (mrestrict (w_H W3) m) a.
Proof.
  intros W3 m m' lo hi a Hk Ha Hn. unfold mbyte, mrestrict. rewrite (Hk a Ha Hn). reflexivity.
Qed.
Lemma l7_keep_writable : forall (W3 : world tfibsegs) (m m' : word -> option byte) (lo hi a : Z),
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  writable_at tfibsegs (mrestrict (w_H W3) m) a -> writable_at tfibsegs (mrestrict (w_H W3) m') a.
Proof.
  intros W3 m m' lo hi a Hk Ha Hn Hw. unfold writable_at, wview, mrestrict in *.
  rewrite (Hk a Ha Hn). exact Hw.
Qed.
(* a boundary region whose extent misses the write window is carried across it *)
Lemma l7_keep_region : forall (W3 : world tfibsegs) E (m m' : word -> option byte) (lo hi : Z) r,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
  YP09.r_lo r <= YP09.r_wlo r -> YP09.r_whi r <= YP09.r_hi r ->
  Forall (fun c => YP09.r_lo r <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= YP09.r_hi r) (YP09.r_chunks r) ->
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi)) ->
  region_ok tfibsegs E (mrestrict (w_H W3) m) r -> region_ok tfibsegs E (mrestrict (w_H W3) m') r.
Proof.
  intros W3 E m m' lo hi r Hk Hwl Hwh Hci Hout (B1 & B2 & Hw & Hc).
  split; [exact B1|]. split; [exact B2|]. split.
  - intros o Ho. destruct (Hout (base_val E (YP09.r_base r) + o) ltac:(lia)) as (Ha & Hn).
    exact (l7_keep_writable W3 m m' lo hi _ Hk Ha Hn (Hw o Ho)).
  - rewrite Forall_forall in Hc, Hci |- *. intros c Hin.
    destruct (Hci c Hin) as (Hc1 & Hc2).
    apply (chunk_ok_mbyte E (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') _ c); [|exact (Hc c Hin)].
    intros i Hi. destruct (Hout (base_val E (YP09.r_base r) + YP09.c_off c + i) ltac:(lia)) as (Ha & Hn).
    exact (l7_keep_byte W3 m m' lo hi _ Hk Ha Hn).
Qed.

(* ---- the loop's write window misses all four boundary regions ----
   the stack pair by alloc_ceiling (the stack lies above it, crt_sb's facts), the frame by AR's block / frame
   separation (YCbq.sep_block_frame), its shadow because an application byte is never a shadow byte ---- *)
Lemma l7_sep : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 same ps ks n,
  crt_base B cx -> crt_E cx E ->
  crt_J SK B cx ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k -> ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  In (ps, ks) (ablocks B ly3 S3) -> ps <= same -> same + n <= ps + ks -> 0 <= n ->
  (forall a, same <= a < same + n ->
     0 <= a < 2 ^ 64 /\
     ~ (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) /\
     ~ (crt_sp1 cx + 0x10 <= a < crt_sp1 cx + 0x58) /\
     ~ (crt_F cx <= a < crt_F cx + fs_frame_bytes 3) /\
     ~ (crt_SF cx <= a < crt_SF cx + fs_frame_bytes 3 / 8)).
Proof.
  intros cx E k ly3 S3 U3 W3 ms3 md3 same ps ks n HB HE HJ HARU Hfr Hin Hlo Hhi Hn.
  pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
  pose proof HB as (HPRE & _).
  pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hal16 & Hceil0 & H47 & HS0).
  pose proof crt_STK_eq as STKv; unfold crt_STK in STKv.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
    as (F1 & F2 & F3).
  assert (Hsp1 : spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
  pose proof (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfr) as (FA & F4096 & Fceil & Fapp & FS1 & FS2).
  pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 ps ks HAR Hin)
    as (_ & P4096 & Pceil & Papp & _ & _ & Pn).
  pose proof HJ as (_ & Hly & _). pose proof (crt_F_ly cx _ ly3 Hly) as EF.
  assert (Hks : ks <= req_size ks) by (unfold req_size; destruct (Z.eqb_spec ks 0); lia).
  assert (HFsep : zdisjoint (ps, req_size ks) (crt_F cx, fs_frame_bytes 3)).
  { rewrite <- EF.
    exact (sep_block_frame tfibsegs B LAWS ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 ps ks 3 (c_pos cx) HAR Hin
             ltac:(rewrite Hfr; left; reflexivity)). }
  unfold zdisjoint in HFsep. cbn [fst snd] in HFsep.
  rewrite crt_frame3 in *.
  intros a Ha.
  assert (Happ : in_app a 1) by (eapply in_app_sub; [exact Papp | lia | lia | lia]).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros Hsh. apply (l7_app_not_shadow a Happ). unfold crt_SF, shadow_addr in *.
  unfold SHADOW_OFF, kHighMemBeg, kHighShadowEnd, kLowMemEnd in *. lia.
Qed.

(* the four boundary regions are disjoint under any env that gives their bases the same values *)
Lemma l7_pd_agree : forall E1 E2 (rs : smem),
  (forall r, In r rs -> base_val E1 (YP09.r_base r) = base_val E2 (YP09.r_base r)) ->
  pairwise_disjoint E1 rs -> pairwise_disjoint E2 rs.
Proof.
  intros E1 E2 rs. induction rs as [|r rs IH]; cbn; intros Hb H; [exact I|].
  destruct H as (Had & Hpd). split.
  - clear Hpd IH. induction rs as [|r' rs IH']; cbn in Had |- *; [exact I|].
    destruct Had as (Hd & Had). split.
    + unfold extent_disjoint in Hd |- *.
      rewrite <- (Hb r ltac:(left; reflexivity)), <- (Hb r' ltac:(right; left; reflexivity)). exact Hd.
    + apply IH'; [intros x Hx; apply Hb; destruct Hx as [<-|Hx]; [left; reflexivity | right; right; exact Hx] | exact Had].
  - apply IH; [intros x Hx; apply Hb; right; exact Hx | exact Hpd].
Qed.

(* l7_pre at the end of the text is b64_strip of the whole text *)
Lemma l7_pre_all : forall tb : list byte, l7_pre tb (Z.of_nat (length tb)) = B64Canon.b64_strip (HState.zs tb).
Proof.
  intros tb. unfold l7_pre. rewrite Nat2Z.id, firstn_all2 by (rewrite l7_zs_len; lia). reflexivity.
Qed.

(* The stability predicate this lemma takes is the base's crt_stable7E (lib/B/FSH_crt_base.v, B base v25): the boundary
   env is free on both sides, because a boundary state has every register as an atom and the loop changes t0 t1 a0 a1
   a3 a7 s9 (A: a0 a1 a2 a5 a6 a7 s9), so the exit is read under E' = Ereg regs' (crt_extra cx), not under E. *)
(* ---- lane L7: the segment lemma, frame-generic in R ---- *)
Theorem crt_l7_seg : forall R : crt_inv,
  crt_stable7E R ->
  crt_from SK B (crt_ss_ret L7_EXIT crt_cs1 crt_csF)
    (fun cx E k ly3 S3 U3 W3 ms3 md3 =>
       crt_INV_82028 cx E k ly3 S3 U3 W3 ms3 md3 /\ R cx E k ly3 S3 U3 W3 ms3 md3) ->
  crt_from SK B (crt_ss_ret L7_HEAD crt_cs1 crt_csF)
    (fun cx E k ly3 S3 U3 W3 ms3 md3 =>
       crt_INV_81fb8 B cx E k ly3 S3 U3 W3 ms3 md3 /\ R cx E k ly3 S3 U3 W3 ms3 md3).
Proof.
  intros R HST HNEXT cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFR (HINV & HR) HS.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HINV as (same & R25 & R13 & R11 & R24 & R18 & R14 & R16 & R12 & R15 & HTXT & HSlo & HShi & HWRa &
                    (pt & kt & HTBi & HTLO & HTHI) & (ps & ks & HSBi & HSLO & HSHI) & HDJ & HNZ & HTU & HSU).
  pose proof HFR as (Hfr & Hfr2 & Hflag).
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HLENb & _).
  assert (HLEN : Z.of_nat (length (c_tb cx)) <= 3145728) by (change (3 * 2 ^ 20) with 3145728 in HLENb; lia).
  assert (Hks : ks <= req_size ks) by (unfold req_size; destruct (Z.eqb_spec ks 0); lia).
  assert (Hkt : kt <= req_size kt) by (unfold req_size; destruct (Z.eqb_spec kt 0); lia).
  (* the loop's premises, from the boundary invariant *)
  assert (HTUP : l7_unp U3 (c_t cx) (Z.of_nat (length (c_tb cx)) + 1)).
  { unfold l7_unp. rewrite Forall_forall in HTU |- *. intros q Hq. destruct (HTU q Hq); [left | right]; lia. }
  assert (HSUP : l7_unp U3 same (Z.of_nat (length (c_tb cx)) + 1)).
  { unfold l7_unp. rewrite Forall_forall in HSU |- *. intros q Hq. destruct (HSU q Hq); [left | right]; lia. }
  (* the machine state at the head, in the shape the loop lemma runs from *)
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E (crt_ss_ret L7_HEAD crt_cs1 crt_csF) ms3 HS eq_refl).
  cbn [crt_ss_ret fss_ret_s0_args ss_pc].
  apply (crt_l7 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
           (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 k W3
           (c_t cx) same (c_tb cx) pt kt ps ks
           HTBi HTLO ltac:(lia) HSBi HSLO ltac:(lia) HDJ
           ltac:(intros a Ha; exact (proj2 (HWRa a Ha))) HNZ HLEN HTUP HSUP
           (ms_regs ms3) (ms_mem ms3) md3 _).
  - (* the invariant at trip 0 *)
    split; [exact HJ|]. split; [exact HARU|]. split; [exact HTXT|].
    rewrite (proj1 (l7_j0 (c_tb cx))).
    split; [intros jj Hjj; cbn [length] in Hjj; exfalso; lia|].
    rewrite (proj2 (l7_j0 (c_tb cx))).
    split; [rewrite R25; f_equal; lia|]. split; [rewrite R13; f_equal; lia|].
    split; [exact R11|]. split; [exact R24|]. split; [exact R18|].
    split; [exact R14|]. split; [exact R16|]. split; [exact R12 | exact R15].
  - (* at the exit: the four boundary regions are carried across the loop's one write window *)
    intros regs' mem' md' HAT' HKEPT HMF.
    destruct HAT' as (HJ' & HARU' & HTXT' & HPRE' & R25' & R13' & R11' & R24' & R18' & R14' & R16' & R12' & R15').
    (* the machine's registers at the head, read off the boundary state's atoms *)
    assert (Ea : forall (r : bv 5) (m : nat),
              sr_get (ss_regs (crt_ss_ret L7_HEAD crt_cs1 crt_csF)) r = SOff m 0 ->
              YK11.getr (ms_regs ms3) r = ew E m).
    { intros r m Hr. rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms3 r HS), Hr, fsw_SOff0. reflexivity. }
    assert (K2 : YK11.getr regs' 2%bv = ew E 2)
      by (rewrite (HKEPT 2%bv ltac:(cbn [L7_KEPT In]; tauto)); apply Ea; vm_compute; reflexivity).
    assert (K3 : YK11.getr regs' 3%bv = ew E 3)
      by (rewrite (HKEPT 3%bv ltac:(cbn [L7_KEPT In]; tauto)); apply Ea; vm_compute; reflexivity).
    assert (K4 : YK11.getr regs' 4%bv = ew E 4)
      by (rewrite (HKEPT 4%bv ltac:(cbn [L7_KEPT In]; tauto)); apply Ea; vm_compute; reflexivity).
    assert (K8 : YK11.getr regs' 8%bv = ew E 8)
      by (rewrite (HKEPT 8%bv ltac:(cbn [L7_KEPT In]; tauto)); apply Ea; vm_compute; reflexivity).
    assert (K9 : YK11.getr regs' 9%bv = ew E 9)
      by (rewrite (HKEPT 9%bv ltac:(cbn [L7_KEPT In]; tauto)); apply Ea; vm_compute; reflexivity).
    assert (K26 : YK11.getr regs' 26%bv = ew E 26)
      by (rewrite (HKEPT 26%bv ltac:(cbn [L7_KEPT In]; tauto)); apply Ea; vm_compute; reflexivity).
    (* the exit env: the registers the loop left, and crt_extra unchanged *)
    assert (HE' : crt_E cx (Ereg regs' (crt_extra cx))).
    { pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & EX).
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      - rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl), K2. exact E2.
      - rewrite (ew_Ereg_nat regs' _ 3 3%bv eq_refl), K3. exact E3.
      - rewrite (ew_Ereg_nat regs' _ 4 4%bv eq_refl), K4. exact E4.
      - rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), K8. exact E8.
      - rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), K9. exact E9.
      - rewrite (ew_Ereg_nat regs' _ 26 26%bv eq_refl), K26. exact E26.
      - intros j Hj. rewrite ew_Ereg_extra. reflexivity. }
    (* the atoms the four regions and the boundary facts read keep their values *)
    assert (AGE : forall m, l7_PA m = true -> ew (Ereg regs' (crt_extra cx)) m = ew E m).
    { pose proof HE as (_ & _ & _ & _ & _ & _ & EX).
      intros m Hm. unfold l7_PA in Hm.
      destruct (Nat.eqb m 8) eqn:Q8;
        [apply Nat.eqb_eq in Q8; subst m; rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact K8|].
      destruct (Nat.eqb m 9) eqn:Q9;
        [apply Nat.eqb_eq in Q9; subst m; rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl); exact K9|].
      destruct (Nat.eqb m 26) eqn:Q26;
        [apply Nat.eqb_eq in Q26; subst m; rewrite (ew_Ereg_nat regs' _ 26 26%bv eq_refl); exact K26|].
      cbn [orb] in Hm. apply andb_prop in Hm as (Hm1 & Hm2).
      apply Nat.leb_le in Hm1. apply Nat.ltb_lt in Hm2.
      replace m with (32 + (m - 32))%nat by lia.
      rewrite ew_Ereg_extra, (EX (m - 32)%nat ltac:(lia)). reflexivity. }
    (* the loop's write window misses every boundary region *)
    pose proof (l7_sep cx E k ly3 S3 U3 W3 ms3 md3 same ps ks (Z.of_nat (length (c_tb cx)) + 1)
                  HB HE HJ HARU Hfr HSBi HSLO ltac:(lia) ltac:(lia)) as HSEP.
    pose proof HE as (_ & _ & _ & EE8 & EE9 & EE26 & _).
    pose proof (crt_E_F cx E HE) as EE47.
    pose proof (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfr)
      as (_ & F4096 & Fceil & _ & _ & _).
    pose proof alloc_ceiling_val as HAC.
    assert (EE47u : bv_unsigned (ew E 47) = crt_F cx)
      by (rewrite EE47; apply unsigned_lit_small; rewrite crt_frame3 in *; lia).
    (* the boundary regions at the entry *)
    pose proof (st_ok_mem_ok tfibsegs E _ _ HS) as (Hwf & Hrok & Hpd).
    cbn [crt_ss_ret fss_ret_s0_args fss_ret_s0_regs crt_ret_regions ss_mem ss_regs ss_facts] in Hwf, Hrok, Hpd.
    assert (HSb : forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 -> False -> False) by (intros; assumption).
    (* each region, carried across the window *)
    assert (RK : forall r, In r [crt_s0_region; crt_slot_region crt_cs1; crt_frame_region crt_csF; crt_shadow_region] ->
             region_ok tfibsegs (Ereg regs' (crt_extra cx)) (mrestrict (w_H W3) mem') r).
    { intros r Hin.
      assert (Hbase : base_val (Ereg regs' (crt_extra cx)) (YP09.r_base r) = base_val E (YP09.r_base r)).
      { cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
          cbn [crt_s0_region fs_ret_s0_region crt_slot_region crt_frame_region crt_shadow_region YP09.r_base base_val];
          [rewrite (AGE 8%nat eq_refl) | rewrite (AGE 9%nat eq_refl) | rewrite (AGE 47%nat eq_refl)
           | rewrite (AGE 26%nat eq_refl)]; reflexivity. }
      apply (region_ok_agree_on tfibsegs l7_PA E (Ereg regs' (crt_extra cx)));
        [ exact AGE
        | cbn [In] in Hin; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity
        | ].
      rewrite Forall_forall in Hrok.
      apply (l7_keep_region W3 E (ms_mem ms3) mem' same (same + Z.of_nat (length (c_tb cx)) + 1) r);
        [ intros x Hx Hn; exact (HMF x Hx Hn)
        | cbn [In] in Hin; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia
        | cbn [In] in Hin; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia
        | cbn [In] in Hin; destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
          unfold crt_s0_region, fs_ret_s0_region, crt_slot_region, crt_frame_region, crt_shadow_region,
            crt_sv_chunks, crt_cs1, crt_csF;
          cbn [YP09.r_chunks YP09.r_lo YP09.r_hi map seq];
          repeat (apply Forall_cons; [cbn; pose proof crt_frame3; lia|]); apply Forall_nil
        | intros a Ha;
          pose proof (Hrok r ltac:(cbn [In]; tauto)) as (RB1 & RB2 & _ & _);
          split; [lia|];
          intros Hc; destruct (HSEP a ltac:(clear - Hc; lia)) as (_ & Hw2 & Hw3 & Hw4 & Hw5); revert Ha;
          cbn [In] in Hin; destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
          cbn [crt_s0_region fs_ret_s0_region crt_slot_region crt_frame_region crt_shadow_region
               YP09.r_base YP09.r_lo YP09.r_hi base_val];
          [rewrite EE8 | rewrite EE9 | rewrite EE47u | rewrite EE26]; intros Ha';
          [exact (Hw2 ltac:(lia)) | exact (Hw3 ltac:(lia)) | exact (Hw4 ltac:(lia)) | exact (Hw5 ltac:(lia))]
        | exact (Hrok r ltac:(cbn [In]; tauto)) ]. }
    (* the boundary state at the exit *)
    assert (HS' : st_ok tfibsegs (Ereg regs' (crt_extra cx)) (crt_ss_ret L7_EXIT crt_cs1 crt_csF)
                    (restrict (w_H W3) (mkst regs' (Z_to_bv 64 L7_EXIT) mem' (seg_rom tfibsegs)))).
    { rewrite restrict_mkst_fx. unfold crt_ss_ret, fss_ret_s0_args, fss_ret_s0_regs.
      apply (entry_st_ok_full tfibsegs).
      - apply regs_ok_Ereg.
      - exact Hwf.
      - apply Forall_forall. intros r Hin. apply RK. cbn [In crt_ret_regions] in Hin |- *. tauto.
      - apply (l7_pd_agree E); [|exact Hpd].
        intros r Hin. cbn [In crt_ret_regions] in Hin.
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
          cbn [crt_s0_region fs_ret_s0_region crt_slot_region crt_frame_region crt_shadow_region YP09.r_base base_val];
          [rewrite (AGE 8%nat eq_refl) | rewrite (AGE 9%nat eq_refl) | rewrite (AGE 47%nat eq_refl)
           | rewrite (AGE 26%nat eq_refl)]; reflexivity.
      - pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & Hfacts).
        unfold crt_ss_ret, fss_ret_s0_args, crt_ret_facts in Hfacts.
        cbn [ss_facts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok] in Hfacts |- *.
        destruct Hfacts as ((F8 & F9 & F47 & _) & _).
        split; [|split; exact I].
        split; [|split; [|split; [|exact I]]].
        + unfold afact_ok in F8 |- *. rewrite (AGE 8%nat eq_refl). exact F8.
        + unfold afact_ok in F9 |- *. rewrite (AGE 9%nat eq_refl). exact F9.
        + unfold afact_ok in F47 |- *. rewrite (AGE 47%nat eq_refl). exact F47. }
    (* the frame's flag word is outside the window, so crt_frame_ok crosses *)
    assert (HFR' : crt_frame_ok cx S3 W3 (mkst regs' (Z_to_bv 64 L7_EXIT) mem' (seg_rom tfibsegs))).
    { split; [exact Hfr|]. split; [exact Hfr2|]. cbn [ms_mem mkst].
      rewrite <- Hflag. apply rdword_ext. intros i Hi. unfold aview. f_equal.
      apply (l7_keep_byte W3 (ms_mem ms3) mem' same (same + Z.of_nat (length (c_tb cx)) + 1));
        [ intros x Hx Hn; exact (HMF x Hx Hn) | | ].
      - rewrite crt_frame3 in *. clear - F4096 Fceil HAC Hi. lia.
      - intros Hc. destruct (HSEP (crt_F cx + fs_frame_bytes 3 - 8 + i)) as (_ & _ & _ & Hw4 & _);
          [lia | apply Hw4; rewrite crt_frame3 in *; lia]. }
    (* the output buffer stays writable: its bytes are a live block's, through ARU at the exit memory *)
    assert (HWin : forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 ->
                     writable_at tfibsegs (mrestrict (w_H W3) mem') a).
    { intros a Ha. pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU') as HAR'.
      destruct (al_blocks _ _ LAWS ly3 S3 W3 (unpoison U3 mem') md' ps ks HAR' HSBi)
        as (_ & _ & _ & _ & Hpres & _ & _).
      destruct (Hpres a ltac:(assert (ks <= req_size ks) by (unfold req_size; destruct (Z.eqb_spec ks 0); lia); lia))
        as (Hp & Hno).
      apply (apresent_writable tfibsegs).
      exact (fsw_apresent_notowned B ly3 S3 U3 W3 mem' md' a HARU' ltac:(lia) Hno Hp). }
    (* hand the exit boundary to the next segment *)
    apply (HNEXT cx (Ereg regs' (crt_extra cx)) k ly3 S3 U3 W3
             (mkst regs' (Z_to_bv 64 L7_EXIT) mem' (seg_rom tfibsegs)) md' HB HE' HJ' HARU' HFR'); [|exact HS'].
    split.
    + exists same. cbn [ms_regs ms_mem mkst].
      split; [exact R25'|]. split; [exact R13'|].
      split; [rewrite R11'; unfold l7_j; rewrite l7_pre_all; reflexivity|].
      split; [exact R24'|]. split; [exact R18'|]. split; [exact R14'|]. split; [exact R16'|].
      split; [exact R12'|]. split; [exact R15'|].
      split; [rewrite <- l7_pre_all; exact HPRE'|]. split; [exact HTXT'|].
      split; [exact HSlo | exact HShi].
    + exact (HST cx E (Ereg regs' (crt_extra cx)) k ly3 S3 U3 W3 ms3 md3
               (mkst regs' (Z_to_bv 64 L7_EXIT) mem' (seg_rom tfibsegs)) md' same HE HE' R24 HR
               (conj ltac:(intros r Hr; cbn [ms_regs mkst]; apply HKEPT; unfold crt_kept7 in Hr; exact Hr)
                  (conj ltac:(intros a Ha Hn; cbn [ms_mem mkst]; exact (HMF a Ha Hn)) HWin))).
Qed.
End Seg.
