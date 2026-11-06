(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS1.v at ad46b8b766a1; the same walk for
   image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan and the kit is image B's (RtPgStepsB, RtPgMemB,
   RtPgCcsvCutB, RtPgCcsvMB, RtPgCcsvKitB); the segment, the run table and the registers are image B's; the frame F is
   an extra atom of the environment (no register holds it); closed_list after the frame call comes from
   RtPgCSpec.rt_img_facts at image B's record (RtPgCcsvKitB part (7)) instead of image A's RtPgSiteA facts; the four
   bound tests of image B's undefined-behaviour checks are decided by the run. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address below is measured on its unstripped
   twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded bytes are the same):
   segment S1 of the walk of check_csv (0x837c0), that is the three passes 0x83948 .. 0x83a90, against
   RtPgCcsvCutB.CC_S1_stmt. Proves no function (kind: segment lemma).

   The code of the segment, by address (registers: a2 = i, t3 = n, s6 = mask, s8 = want = F + 32, a3 = d = F + 112,
   s3 = F + 111, s7 = shadow_addr F, s9 = SHADOW_OFF, t4 = 0x21520 = closed_list, a6 = 3, a7 = 8, a4 = -8; no
   register holds F):
     0x83948 `srlw a0,s6,a2; andi a0,a0,1; beqz a0 -> 0x83a74`   bit i of mask: UNDECIDED, see below
     0x83954 .. 0x83970  closed_list[i] through an instrumented 4-byte load (slow block 0x83a80 .. 0x83a88)
     0x83974 `sb zero,14(s7)`  d comes into scope (frame-shadow granule 14 := 0)
     0x83978 .. 0x839bc  the do-while digit loop (5 turns per rate): the bound test `beq s10,a7 -> 0x83c70` (k = 8),
                         then an instrumented 1-byte store check (slow block 0x839c4 .. 0x839cc) and the store d[k]
     0x839d0 .. 0x839e8  the comma at want + n when n <> 0, after the bound test `bltu t2,t3 -> 0x83c70` (n > 39)
     0x839fc .. 0x83a4c  the reverse copy d[k-1] .. d[0] into want: the bound tests `bltu a7,s10 -> 0x83c70`
                         (k > 8) and `beqz a0 -> 0x83c70` (a0 = n' + j - 40), then two instrumented checks per byte
                         (slow blocks 0x83a54 .. 0x83a5c and 0x83a60 .. 0x83a68)
     0x83a6c `sb a4,14(s7)`  d leaves scope (granule 14 := 0xf8); 0x83a70 `add t3,s11,t3`
     0x83a74 `addi a2,a2,1`; 0x83a78 `bne a2,a6 -> 0x83948`, else 0x83a7c `j 0x83a90`
   The slow blocks and the error-path arms 0x83cb4 / 0x83cb8 / 0x83cbc / 0x83a8c are not reached, except 0x83a80,
   whose `blt s2,a5` goes back to 0x8396c when the table's granule is not fully usable; the four bound tests to the
   `unimp` 0x83c70 are not taken: k, n, n' + j are literals of each run, so the run decides each of them by itself.
   All of this is decided by the symbolic run, which stops at no branch it cannot decide.

   How the run is set up (one `sym_run_toN_sh` per case, lib/Reusable/YP0i.v through lib/AU/RtPgCcsvKitB.v):
   - the frame F is the extra atom 33 of the environment (no register holds it at the cut: s8 = F + 32, a3 = F + 112,
     s3 = F + 111 are offsets of it), the frame and its shadow are two regions based at the atoms 33 and 23
     (s7 = shadow_addr F), with the alias pair of YP0i `shadow_norm` between them (YP0i shadow_decl_ok), so every
     instrumented check's recomputed address (x >> 3) + s9 resolves to an offset of atom 23;
   - closed_list is a base-free region of three 4-byte literals, from the AR-state invariant (see below), and
     its two shadow granules are a region based at the atom 25 (s9 = SHADOW_OFF) holding the literal 0 (granule
     [0x21520, 0x21528), whose four last bytes are usable, so its shadow byte can only be 0) and the value k1 of
     granule [0x21528, 0x21530), the extra atom 32;
   - the three undecided `beqz a0` of the bit test are decided by three assumed conditions (YP0m f_conds) on the
     register s6's atom, discharged from `Z.testbit mask i` by RtPgCcsvMB `ccsv_bit_sv`; the eight values of
     `mask mod 8` are RtPgCcsvMB `ccsv_mod8_cases`, their bits and lists `ccsv_case0` .. `ccsv_case7`;
   - when bit 2 is set the table's second granule is read, and its shadow byte k1 is only known to be 0 or in
     [4, 8) (RtPgMemB `rtmb_ra_cell4`), which the engine cannot decide: those four cases are split once more, into
     k1 = 0 (the fast arm, the shadow cell a literal 0) and 4 <= k1 < 8 (the slow block 0x83a80, decided from the
     atom fact). Twelve runs in all.

   The section hypotheses, each closed later by the file named:
   - LAWS : AR_laws rsegs B -- lib/Reusable/YG0q.v AR_laws_ok (a theorem).
   - HIMG : rt_img_facts rsegs B rate_himg_B IMG_LO IMG_TOP (RtPgCSpec.rt_img_facts at image B's record
     RtPgImgB.rate_himg_B, range of lib/Reusable/YImgTop.v): the read ranges hold no owned static, the registered
     globals are marked, the image's shadow is visible; image B's close proves it at its symbol record.
     The contract's rt_i32tab premise holds at the CALL only: the class-2 side-stack frame the prologue takes may
     change any byte the runtime owns, and the whole low shadow is owned (YG0n.v `aowned`'s lm_zone disjunct), so
     range_addressable and the values do not reach this segment by themselves. RtPgCcsvKitB `rckb_i32tab_at`
     rebuilds the table at the segment's own state from HIMG, the call's premise and the bytes the cut's keep clause
     carries; `rt_img_unowned` (RtPgBase.v) with RtPgCcsvKitB `rckb_i32_unowned` pays the keep clause's "not owned"
     side condition. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0q YG0s YF0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgStepsB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCcsvCutB RtPgCcsvMB RtPgCcsvKitB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the symbolic state of a pass ======================================== *)
(* the 82 instruction words of [0x83948, 0x83a90): the three passes, their slow blocks and the joins *)
Definition s1_tbl : ctable := build_table rsegs CC_PC1 82 TEmpty.
Lemma s1_tbl_ok : table_ok rsegs s1_tbl.
Proof. apply build_table_ok0. unfold CC_PC1. lia. Qed.

(* YP0i shadow_norm's alias pair for the frame: (F >> 3) + s9 is the atom of s7 = shadow_addr F, F the atom 33 *)
Definition s1_alias : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 25 0), SOff 23 0).

(* the registers cc_st1 fixes: a3, s3, s8 as offsets of the frame atom 33, the literals t0, t1, t2, a2, a4, a6, a7,
   t3, t4, t5, t6; every other register keeps its own atom *)
Definition s1_sr : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set
  sr_atoms
  (5%bv : bv 5) (SLit 10)) (6%bv : bv 5) (SLit 18)) (7%bv : bv 5) (SLit 39))
  (12%bv : bv 5) (SLit 0)) (13%bv : bv 5) (SOff 33 112)) (14%bv : bv 5) (SLit 18446744073709551608))
  (16%bv : bv 5) (SLit 3)) (17%bv : bv 5) (SLit 8)) (19%bv : bv 5) (SOff 33 111))
  (24%bv : bv 5) (SOff 33 32)) (28%bv : bv 5) (SLit 0)) (29%bv : bv 5) (SLit CC_TCL))
  (30%bv : bv 5) (SLit 0x66666667)) (31%bv : bv 5) (SLit 44).

(* the 32 shadow bytes of the class-2 frame at the cut (CC_SH_A and the allocator's zeroes) *)
Definition s1_fsh_pat : list Z := CC_SH_A ++ repeat 0 12.

(* the frame's object bytes (want[40] at +32, d[8] at +112: the pass writes inside [32, 120)) *)
Definition s1_rframe : YP09.region := YP09.mkRegion (Some 33%nat) 32 120 32 120 [].
(* the frame's shadow bytes, the only shadow byte the pass writes being granule 14 *)
Definition s1_rfsh : YP09.region := YP09.mkRegion (Some 23%nat) 0 32 14 15 (rtmb_fsh_cs s1_fsh_pat).
(* closed_list's two shadow granules, as offsets of the atom of s9 = SHADOW_OFF *)
Definition s1_rclsh (e1 : sv) : YP09.region :=
  YP09.mkRegion (Some 25%nat) 0x42a4 (0x42a4 + 2) 0 0
  [YP09.mkChunk 0x42a4 (CVal 1 (SLit 0)); YP09.mkChunk (0x42a4 + 1) (CVal 1 e1)].
(* closed_list itself: three 4-byte literals in the image's read-only PT_LOAD *)
Definition s1_rcl : YP09.region :=
  YP09.mkRegion None CC_TCL (CC_TCL + 12) 0 0
  [YP09.mkChunk CC_TCL (CVal 4 (SLit 44100));
   YP09.mkChunk (CC_TCL + 4) (CVal 4 (SLit 48000));
   YP09.mkChunk (CC_TCL + 8) (CVal 4 (SLit 96000))].
Definition s1_mem (e1 : sv) : smem := [s1_rframe; s1_rfsh; s1_rclsh e1; s1_rcl].

(* the bit test `srlw a0,s6,i; andi a0,a0,1` as the engine leaves it, and the assumed branch of `beqz a0` *)
Definition s1_ebit (i : Z) : sv := SAlu ALU_AND (SAluw ALU_SRL (SOff 22 0) (SLit i)) (SLit 1).
Definition s1_bc (b : bool) (i : Z) : acond := mkAC (if b then BC_NE else BC_EQ) (s1_ebit i) (SLit 0).
Definition s1_conds (b0 b1 b2 : bool) : list acond := [s1_bc b0 0; s1_bc b1 1; s1_bc b2 2].

(* the frame atom's bounds (4096 <= F, F 32-aligned: YP0i shadow_norm asks 3 <= af_al2) and closed_list's
   second shadow granule, whose value is the atom 32 *)
Definition s1_facts (b0 b1 b2 : bool) (fk : afact) : facts :=
  mkFacts [(33%nat, mkAF 4096 (2 ^ 47) 5); (32%nat, fk)] (s1_conds b0 b1 b2) [s1_alias].
Definition s1_ss (b0 b1 b2 : bool) (fk : afact) (e1 : sv) : sstate :=
  mkSS CC_PC1 s1_sr (s1_mem e1) None (s1_facts b0 b1 b2 fk).

(* ======================================== reading a run's final state ======================================== *)
(* the literal byte a region's chunk list holds at the offset o, when it holds one *)
Fixpoint s1_cbyte (cs : list YP09.chunk) (o : Z) : option Z :=
match cs with
| [] => None
| c :: cs' =>
  match YP09.c_val c with
  | CVal w (SLit v) => if (N.eqb w 1 && (YP09.c_off c =? o))%bool then Some v else s1_cbyte cs' o
  | _ => s1_cbyte cs' o
  end
end.

Lemma s1_cbyte_in : forall cs o v, s1_cbyte cs o = Some v -> In (YP09.mkChunk o (CVal 1 (SLit v))) cs.
Proof.
induction cs as [|c cs IH]; intros o v H; cbn [s1_cbyte] in H; [discriminate|].
destruct c as [co cv]. cbn [YP09.c_val YP09.c_off] in H.
destruct cv as [w e| | |]; try (right; exact (IH o v H)).
destruct e as [z| | | | | | | | | |]; try (right; exact (IH o v H)).
destruct (N.eqb w 1 && (co =? o))%bool eqn:Hb; [|right; exact (IH o v H)].
apply andb_prop in Hb as [Hw Ho]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Ho.
injection H as <-. subst. left. reflexivity.
Qed.

Lemma s1_bv8_eq : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. exact H.
Qed.

Lemma s1_wrap64_256 : forall x, bv_wrap 64 x mod 256 = x mod 256.
Proof.
intros x. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). symmetry.
apply Znumtheory.Zmod_div_mod; [lia | lia | exists 72057594037927936; vm_compute; reflexivity].
Qed.

(* the byte a region's literal chunk gives, as the memory reads it *)
Lemma s1_cbyte_mbyte : forall E m r o v,
  region_ok rsegs E m r -> s1_cbyte (YP09.r_chunks r) o = Some v ->
  mbyte rsegs m (base_val E (YP09.r_base r) + o) = Some (Z_to_bv 8 v).
Proof.
intros E m r o v HR Hc.
pose proof (region_ok_chunk rsegs E m r _ HR (s1_cbyte_in _ _ _ Hc)) as HC.
destruct (HC 0 ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. rewrite Z.add_0_r in Hb2.
injection Hb1 as <-. rewrite Hb2. f_equal.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_unsigned.
apply s1_bv8_eq. apply s1_wrap64_256.
Qed.

(* the literal bytes a region holds from the offset base on, as a boolean the kernel decides *)
Definition s1_chk_bytes (cs : list YP09.chunk) (base : Z) (l : list Z) : bool :=
  forallb (fun j => match s1_cbyte cs (base + Z.of_nat j) with
                    | Some v => v mod 256 =? nth j l 0 mod 256
                    | None => false end) (seq 0 (length l)).

Lemma s1_chk_bytes_ok : forall E m r base l,
  region_ok rsegs E m r -> s1_chk_bytes (YP09.r_chunks r) base l = true ->
  forall j, (j < length l)%nat ->
    mbyte rsegs m (base_val E (YP09.r_base r) + base + Z.of_nat j) = Some (Z_to_bv 8 (nth j l 0)).
Proof.
intros E m r base l HR Hb j Hj.
assert (Hin : In j (seq 0 (length l))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hb j Hin) as Hq. cbn beta in Hq.
destruct (s1_cbyte (YP09.r_chunks r) (base + Z.of_nat j)) as [v|] eqn:Hc; [|discriminate Hq].
apply Z.eqb_eq in Hq.
rewrite <- Z.add_assoc. rewrite (s1_cbyte_mbyte E m r _ v HR Hc). f_equal.
apply s1_bv8_eq. exact Hq.
Qed.

(* ======================================== generic engine helpers ======================================== *)
(* a register pinned to any sv whose value it holds, as a regs_ok step (for the cut's symbolic registers) *)
Lemma s1_regs_pin : forall E sr regs (r : bv 5) e,
  bv_eqb r 0 = false -> sv_denot E e = getr regs r -> regs_ok E sr regs -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr0 He H rr.
destruct (base.decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. symmetry. exact He.
- rewrite sr_get_set_other by exact Hne. apply H.
Qed.

(* an offset of an atom, as a literal *)
Lemma s1_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H Hv Hc. rewrite denot_lit_U. f_equal. exact (U_atom_off E n v c H Hv Hc).
Qed.

Lemma s1_den_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z Hz. rewrite denot_lit_U, U_SLit. f_equal. apply zcanon_id. unfold M64. lia. Qed.

(* every byte of the frame's shadow pattern is a byte *)
Lemma s1_fsh_bytes : Forall (fun v => 0 <= v < 256) s1_fsh_pat.
Proof.
unfold s1_fsh_pat, CC_SH_A. cbn [repeat app]. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
Qed.

(* the two extra words of a pass's environment: the shadow byte k1 of closed_list's second granule (atom 32) and
   the frame F (atom 33), which no register holds *)
Definition s1_extra (F k1 : Z) : list word := [w64 k1; w64 F].

Lemma s1_ew32 : forall regs F k1, ew (Ereg regs (s1_extra F k1)) 32 = Z_to_bv 64 k1.
Proof. intros regs F k1. exact (ew_Ereg_extra regs (s1_extra F k1) 0). Qed.

Lemma s1_ew33 : forall regs F k1, ew (Ereg regs (s1_extra F k1)) 33 = Z_to_bv 64 F.
Proof. intros regs F k1. exact (ew_Ereg_extra regs (s1_extra F k1) 1). Qed.

Lemma s1_ewr : forall regs F k1 n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Ereg regs (s1_extra F k1)) n = getr regs r.
Proof. intros regs F k1 n r H. exact (ew_Ereg_nat regs (s1_extra F k1) n r H). Qed.

(* ======================================== the final state's check ======================================== *)
(* the registers cc_st2 and cc_frame ask of the state the run ends in, still their own atoms *)
Definition s1_regchk (ss : sstate) : bool :=
  sv_eqb (sr_get (ss_regs ss) (2%bv : bv 5)) (SOff 2 0) &&
  sv_eqb (sr_get (ss_regs ss) (3%bv : bv 5)) (SOff 3 0) &&
  sv_eqb (sr_get (ss_regs ss) (4%bv : bv 5)) (SOff 4 0) &&
  sv_eqb (sr_get (ss_regs ss) (8%bv : bv 5)) (SOff 8 0) &&
  sv_eqb (sr_get (ss_regs ss) (9%bv : bv 5)) (SOff 9 0) &&
  sv_eqb (sr_get (ss_regs ss) (23%bv : bv 5)) (SOff 23 0) &&
  sv_eqb (sr_get (ss_regs ss) (25%bv : bv 5)) (SOff 25 0).

(* everything cc_st2 asks of the state the run ends in, as one boolean *)
Definition s1_final_ok (ss : sstate) (L : list Z) : bool :=
  (ss_pc ss =? CC_PC2) &&
  (match ss_resv ss with None => true | _ => false end) &&
  s1_regchk ss &&
  sv_eqb (sr_get (ss_regs ss) (24%bv : bv 5)) (SOff 33 32) &&
  sv_eqb (sr_get (ss_regs ss) (28%bv : bv 5)) (SLit (Z.of_nat (length L))) &&
  (match nth_error (ss_mem ss) 0 with
   | Some r => YP09.obase_eqb (YP09.r_base r) (Some 33%nat) && s1_chk_bytes (YP09.r_chunks r) 32 L
   | None => false end) &&
  (match nth_error (ss_mem ss) 1 with
   | Some r => YP09.obase_eqb (YP09.r_base r) (Some 23%nat) && s1_chk_bytes (YP09.r_chunks r) 0 s1_fsh_pat
   | None => false end).

(* ======================================== the walk ======================================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws rsegs B.
(* image B's record of its read-only data; see the file header. *)
Hypothesis HIMG : rt_img_facts rsegs B rate_himg_B IMG_LO IMG_TOP.

Lemma s1_tab_in : In (CC_TCL, RateCfg.closed_list) rate_B_i32.
Proof. exact rckb_tab_in. Qed.

Section w.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sj : astate) (W0 : world rsegs).
Variables (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate).
Variables (W : world rsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word).
Variables (buf n mask fpos : Z) (S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word).
Variables (mem1 : word -> option byte) (md1 : Model).
Hypothesis H1 : cc_st1 B MT STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask
  fpos S1 W1 regs1 mem1 md1.

(* the frame, the extra atom 33 of every pass's environment *)
Local Abbreviation FA := (frame_addr lyc CC_CID fpos).

(* what the cut gives, in the form the run needs *)
Lemma s1_unpack :
  ajournal rsegs B STK sp0 FP ly Sj W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 mem1 md1 k /\
  AR rsegs B lyc S1 W1 mem1 md1 /\ AR rsegs B lyc Sc W memc mdc /\
  In (CC_CID, fpos) (frames S1) /\ ~ In (CC_CID, fpos) (frames Sc) /\ 0 <= fpos < fs_frames CC_CID /\
  4096 <= FA /\ FA + 256 <= alloc_ceiling /\
  FA mod 32 = 0 /\ in_app FA 256 /\
  (forall a, FA <= a < FA + 256 -> apresent (w_H W1) mem1 a) /\
  (forall i, 0 <= i < 32 -> apresent (w_H W1) mem1 (shadow_addr FA + i)) /\
  rt_fsh rsegs (w_H W1) mem1 FA s1_fsh_pat /\
  0 <= mask < 2 ^ 64 /\ 0 <= shadow_addr FA /\
  shadow_addr FA + 32 <= alloc_ceiling /\
  (FA + 256 <= shadow_addr FA \/ shadow_addr FA + 32 <= FA) /\
  alloc_ceiling + STK <= sp0 /\ sp0 <= 2 ^ 47 /\
  sp0 - STK <= spZ regs - T_csv_STK_B /\ spZ regs <= sp0 /\
  rt_i32tab rsegs (w_H W) memc CC_TCL RateCfg.closed_list /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_csv_STK_B <= a < spZ regs) -> ~ aowned B lyc Sc a ->
   aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) /\
  spZ regs mod 16 = 0.
Proof.
destruct H1 as (HP & HFR & Hfsh & _).
destruct HP as (HCP & _ & _ & _ & _ & _ & Hmask & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htab).
destruct HCP as (HJc & _ & _ & _ & _ & Hsp16 & Hsplo & Hsphi & _).
destruct HFR as (HJ & Hfrs & Hnin & _ & _ & _ & _ & _ & _ & _ & _ & Hkeep & HF0 & HF1 & Happ & Hal & _).
pose proof (proj1 HJ) as HAR1. pose proof (proj1 HJc) as HARc.
assert (Hin : In (CC_CID, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frame_facts B lyc S1 (aview rsegs (w_H W1) mem1) CC_CID fpos (proj1 HAR1) Hin) as (_ & Hpos & _).
destruct (al_frames rsegs B LAWS lyc S1 W1 mem1 md1 CC_CID fpos HAR1 Hin) as (_ & _ & Hpres & Hspres).
change (fs_frame_bytes CC_CID) with 256 in Hpres, Hspres.
destruct (rck_fbounds CC_CID FA ltac:(cbv; discriminate) Hal
  ltac:(change (fs_frame_bytes CC_CID) with 256; exact Happ)) as (_ & _ & Hs0 & Hs1 & Hsep & _).
change (256 / 8) with 32 in Hs1, Hsep. change (fs_frame_bytes CC_CID) with 256 in Hs1, Hsep.
pose proof HJ as HJ2.
destruct HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
split; [exact HJ|]. split; [exact HAR1|]. split; [exact HARc|]. split; [exact Hin|]. split; [exact Hnin|].
split; [exact Hpos|]. split; [exact HF0|]. split; [exact HF1|]. split; [exact Hal|]. split; [exact Happ|].
split; [intros a Ha; exact (proj1 (Hpres a Ha))|].
split; [intros i Hi; exact (proj1 (Hspres i Hi))|].
split; [exact Hfsh|]. split; [exact Hmask|]. split; [exact Hs0|]. split; [exact Hs1|]. split; [exact Hsep|].
split; [lia|]. split; [lia|]. split; [exact Hsplo|]. split; [exact Hsphi|].
split; [exact Htab|]. split; [exact Hkeep | exact Hsp16].
Qed.

(* ---- the registers of the cut ---- *)
Lemma s1_regs :
  getr regs1 2 = w64 (cc_rbase (spZ regs)) /\ getr regs1 9 = w64 (cc_rbase (spZ regs)) /\
  getr regs1 5 = w64 10 /\ getr regs1 6 = w64 18 /\ getr regs1 7 = w64 39 /\
  getr regs1 12 = w64 0 /\ getr regs1 13 = w64 (FA + 112) /\ getr regs1 14 = w64 (-8) /\
  getr regs1 16 = w64 3 /\ getr regs1 17 = w64 8 /\
  getr regs1 19 = w64 (FA + 111) /\ getr regs1 22 = w64 mask /\
  getr regs1 25 = w64 SHADOW_OFF /\ getr regs1 28 = w64 0 /\ getr regs1 29 = w64 CC_TCL /\
  getr regs1 30 = w64 0x66666667 /\ getr regs1 31 = w64 44 /\
  getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
  getr regs1 8 = w64 (spZ regs) /\
  getr regs1 23 = w64 (shadow_addr FA) /\ getr regs1 24 = w64 (FA + 32).
Proof.
destruct H1 as (_ & HFR & _ & A2 & A5 & A6 & A7 & A12 & A13 & A14 & A16 & A17 & A19 & A22 & A25 & A28 & A29 & A30 & A31).
destruct HFR as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&G3&G4&G8&G9&G23&G24).
repeat split; assumption.
Qed.

(* ---- closed_list at the segment's own state ---- *)
(* closed_list's bytes are image bytes (the call's rt_i32tab) *)
Lemma s1_tab_img : forall i, 0 <= i < 12 -> in_img rsegs (CC_TCL + i).
Proof.
intros i Hi.
destruct s1_unpack as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& Htab & _).
apply (proj1 Htab). rewrite (ltac:(vm_compute; reflexivity) : Z.of_nat (length RateCfg.closed_list) = 3). lia.
Qed.

(* the bytes of the table are the call's: they are image bytes, far from the stack window, and owned in no AR
   state (RtPgBase rt_img_unowned with RtPgCcsvKitB rckb_i32_unowned) *)
Lemma s1_tab_bytes : forall i, 0 <= i < 4 * Z.of_nat (length RateCfg.closed_list) ->
  aview rsegs (w_H W1) mem1 (CC_TCL + i) = aview rsegs (w_H W) memc (CC_TCL + i).
Proof.
intros i Hi.
assert (Hl : Z.of_nat (length RateCfg.closed_list) = 3) by (vm_compute; reflexivity).
rewrite Hl in Hi.
destruct s1_unpack as (_ & _ & HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & Hsp2 & _ & _ & Hkeep).
pose proof asan_consts as (HC & _).
assert (Himg : in_img rsegs (CC_TCL + i)) by (apply s1_tab_img; lia).
apply Hkeep.
- unfold CC_TCL; change (2 ^ 64) with 18446744073709551616; lia.
- unfold CC_TCL in *; lia.
- apply (rt_img_unowned rsegs B LAWS lyc Sc W memc mdc (CC_TCL + i) HARc Himg).
  exact (proj1 (rckb_i32_unowned B CC_TCL RateCfg.closed_list HIMG s1_tab_in (CC_TCL + i)
    ltac:(rewrite Hl; lia))).
Qed.

Lemma s1_tab1 : rt_i32tab rsegs (w_H W1) mem1 CC_TCL RateCfg.closed_list.
Proof.
destruct s1_unpack as (_ & HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htab & _).
exact (rckb_i32tab_at B CC_TCL RateCfg.closed_list lyc S1 W1 mem1 md1 (w_H W) memc
  HIMG s1_tab_in HAR1 Htab s1_tab_bytes).
Qed.

(* the shadow byte of closed_list's first granule, [0x21520, 0x21528): all eight bytes are usable, and byte 7's
   saddr_ok then forces the byte to be 0 *)
Lemma s1_sh0 : aview rsegs (w_H W1) mem1 (SHADOW_OFF + 0x42a4) = Some 0.
Proof.
destruct s1_tab1 as (_ & _ & _ & HRA).
rewrite (ltac:(vm_compute; reflexivity) : Z.of_nat (length RateCfg.closed_list) = 3) in HRA.
destruct (HRA (CC_TCL + 7) ltac:(unfold CC_TCL; lia)) as (s & Hs & Hok).
unfold shadow_of_addr in Hs.
replace (CC_TCL + 7) with 136487 in Hs by (unfold CC_TCL; lia).
change (136487 / 8) with 17060 in Hs. change 0x42a4 with 17060.
destruct Hok as [->|[Hq1 Hq2]]; [exact Hs|].
exfalso. assert (Hm : (CC_TCL + 7) mod 8 = 7) by (vm_compute; reflexivity). lia.
Qed.

(* the shadow byte of the second granule, [0x21528, 0x21530): 0 or in [4, 8) (four of the twelve bytes usable) *)
Lemma s1_sh1 : exists k1, aview rsegs (w_H W1) mem1 (SHADOW_OFF + 0x42a5) = Some k1 /\
  (k1 = 0 \/ 4 <= k1 <= 7) /\ 0 <= k1 < 256.
Proof.
destruct s1_tab1 as (_ & _ & _ & HRA).
rewrite (ltac:(vm_compute; reflexivity) : Z.of_nat (length RateCfg.closed_list) = 3) in HRA.
assert (HRA4 : range_addressable (aview rsegs (w_H W1) mem1) SHADOW_OFF (CC_TCL + 8) 4)
  by (intros x Hx; apply HRA; unfold CC_TCL in *; lia).
destruct (rtmb_ra_cell4 _ SHADOW_OFF (CC_TCL + 8) HRA4 ltac:(unfold CC_TCL; vm_compute; reflexivity))
  as (s & Hs & Hc).
unfold shadow_of_addr in Hs.
replace (CC_TCL + 8) with 136488 in Hs by (unfold CC_TCL; lia).
change (136488 / 8) with 17061 in Hs. change 0x42a5 with 17061.
exists s. split; [exact Hs|].
destruct (rtmb_aview_val1 rsegs (w_H W1) mem1 _ _ Hs) as [_ Hr].
split; [lia | exact Hr].
Qed.

Lemma s1_tabvals : forall i, 0 <= i < 3 ->
  val_mem rsegs (mrestrict (w_H W1) mem1) (CC_TCL + 4 * i) 4 (nth (Z.to_nat i) RateCfg.closed_list 0).
Proof.
intros i Hi. destruct s1_tab1 as (_ & _ & HV & _).
apply HV. rewrite (ltac:(vm_compute; reflexivity) : Z.of_nat (length RateCfg.closed_list) = 3). exact Hi.
Qed.

(* the frame's bytes are not image bytes (YG0d al_client_img), which puts the frame and its shadow apart from
   closed_list and from closed_list's two shadow granules *)
Lemma s1_frame_not_img : forall a, FA <= a < FA + 256 -> ~ in_img rsegs a.
Proof.
intros a Ha. destruct s1_unpack as (_ & HAR1 & _ & Hin & _).
refine (proj2 (al_client_img rsegs B LAWS lyc S1 W1 mem1 md1 a HAR1 _)).
right. left. exists CC_CID, fpos. split; [exact Hin|]. change (fs_frame_bytes CC_CID) with 256. lia.
Qed.

(* ---- the bytes the pass writes are owned by the runtime at the call ---- *)
Lemma s1_own_obj : forall a, FA <= a < FA + 256 -> aowned B lyc Sc a.
Proof.
intros a Ha.
destruct s1_unpack as (_ & _ & HARc & _ & Hnin & Hpos & _).
destruct H1 as (HP & _).
destruct HP as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hcid&_).
exact (own_free_frame B lyc Sc (aview rsegs (w_H W) memc) CC_CID fpos a (proj1 HARc) Hcid Hpos Hnin
  ltac:(change (fs_frame_bytes CC_CID) with 256; exact Ha)).
Qed.

Lemma s1_own_sh : forall a, shadow_addr FA <= a < shadow_addr FA + 32 -> aowned B lyc Sc a.
Proof.
intros a Ha.
destruct s1_unpack as (_ & _ & HARc & _ & Hnin & Hpos & _).
destruct H1 as (HP & _).
destruct HP as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hcid&_).
exact (own_free_frame_shadow B lyc Sc (aview rsegs (w_H W) memc) CC_CID fpos a (proj1 HARc) Hcid Hpos
  Hnin ltac:(change (fs_frame_bytes CC_CID) with 256; change (256 / 8) with 32; exact Ha)).
Qed.

(* ---- the pass's symbolic registers hold the cut's values ---- *)
Lemma s1_regsok : forall k1, regs_ok (Ereg regs1 (s1_extra FA k1)) s1_sr regs1.
Proof.
intros k1.
destruct s1_unpack as (_ & _ & _ & _ & _ & _ & HF0 & HF1 & _).
destruct s1_regs as (G2 & G9 & G5 & G6 & G7 & G12 & G13 & G14 & G16 & G17 & G19 & G22 & G25 & G28 & G29 & G30
  & G31 & _ & _ & _ & _ & G24).
pose proof asan_consts as (HC & _).
assert (HFb : 0 <= FA < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (E33 : ew (Ereg regs1 (s1_extra FA k1)) 33 = Z_to_bv 64 FA) by (apply s1_ew33).
assert (D13 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 33 112) = getr regs1 13)
  by (rewrite G13, (s1_den_off _ 33 _ 112 E33 HFb ltac:(change (2 ^ 64) with 18446744073709551616; lia)); reflexivity).
assert (D19 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 33 111) = getr regs1 19)
  by (rewrite G19, (s1_den_off _ 33 _ 111 E33 HFb ltac:(change (2 ^ 64) with 18446744073709551616; lia)); reflexivity).
assert (D24 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 33 32) = getr regs1 24)
  by (rewrite G24, (s1_den_off _ 33 _ 32 E33 HFb ltac:(change (2 ^ 64) with 18446744073709551616; lia)); reflexivity).
assert (D5 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 10) = getr regs1 5)
  by (rewrite G5; apply bv_eq; vm_compute; reflexivity).
assert (D6 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 18) = getr regs1 6)
  by (rewrite G6; apply bv_eq; vm_compute; reflexivity).
assert (D7 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 39) = getr regs1 7)
  by (rewrite G7; apply bv_eq; vm_compute; reflexivity).
assert (D12 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 0) = getr regs1 12)
  by (rewrite G12; apply bv_eq; vm_compute; reflexivity).
assert (D14 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 18446744073709551608) = getr regs1 14)
  by (rewrite G14; apply bv_eq; vm_compute; reflexivity).
assert (D16 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 3) = getr regs1 16)
  by (rewrite G16; apply bv_eq; vm_compute; reflexivity).
assert (D17 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 8) = getr regs1 17)
  by (rewrite G17; apply bv_eq; vm_compute; reflexivity).
assert (D28 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 0) = getr regs1 28)
  by (rewrite G28; apply bv_eq; vm_compute; reflexivity).
assert (D29 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit CC_TCL) = getr regs1 29)
  by (rewrite G29; apply bv_eq; vm_compute; reflexivity).
assert (D30 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 0x66666667) = getr regs1 30)
  by (rewrite G30; apply bv_eq; vm_compute; reflexivity).
assert (D31 : sv_denot (Ereg regs1 (s1_extra FA k1)) (SLit 44) = getr regs1 31)
  by (rewrite G31; apply bv_eq; vm_compute; reflexivity).
unfold s1_sr.
repeat (apply s1_regs_pin;
  [ vm_compute; reflexivity
  | first [exact D13 | exact D19 | exact D24 | exact D5 | exact D6 | exact D7 | exact D12 | exact D14
          | exact D16 | exact D17 | exact D28 | exact D29 | exact D30 | exact D31] | ]).
apply regs_ok_Ereg.
Qed.

(* ---- the four regions of the pass are apart ---- *)
Lemma s1_disj :
  (FA + 120 <= shadow_addr FA + 0 \/ shadow_addr FA + 32 <= FA + 32) /\
  (FA + 120 <= SHADOW_OFF + 0x42a4 \/ SHADOW_OFF + (0x42a4 + 2) <= FA + 32) /\
  (FA + 120 <= 0 + CC_TCL \/ 0 + (CC_TCL + 12) <= FA + 32) /\
  (shadow_addr FA + 32 <= SHADOW_OFF + 0x42a4 \/ SHADOW_OFF + (0x42a4 + 2) <= shadow_addr FA + 0) /\
  (shadow_addr FA + 32 <= 0 + CC_TCL \/ 0 + (CC_TCL + 12) <= shadow_addr FA + 0) /\
  (SHADOW_OFF + (0x42a4 + 2) <= 0 + CC_TCL \/ 0 + (CC_TCL + 12) <= SHADOW_OFF + 0x42a4).
Proof.
destruct s1_unpack as (_ & _ & _ & _ & _ & _ & HF0 & HF1 & Hal & Happ & _ & _ & _ & _ & Hs0 & Hs1 & Hsep & _).
pose proof (s1_tab_img 0 ltac:(lia)) as Htimg. rewrite Z.add_0_r in Htimg.
destruct (rtsb_fdiv FA Hal) as [EF ES].
pose proof asan_consts as (HC & _).
destruct Happ as (Hap0 & Hap1).
remember (FA / 32) as q eqn:Hq. clear Hq.
unfold CC_TCL, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
split; [destruct Hsep as [Hd|Hd]; [left | right]; lia|].
split; [destruct Hap1 as [Hlo|[Hhi _]]; [left | right]; lia|].
split.
{ destruct (Z.le_gt_cases (FA + 120) 136480) as [Hle|Hgt]; [left; lia|].
  destruct (Z.le_gt_cases 136492 (FA + 32)) as [Hge|Hlt]; [right; lia|].
  exfalso. apply (s1_frame_not_img 136480 ltac:(lia)). exact Htimg. }
split.
{ destruct (Z.le_gt_cases (4 * q + 32) 17060) as [Hle|Hgt]; [left; lia|].
  destruct (Z.le_gt_cases 17062 (4 * q)) as [Hge|Hlt]; [right; lia|].
  exfalso. apply (s1_frame_not_img 136480 ltac:(lia)). exact Htimg. }
split; [right; lia | right; lia].
Qed.

(* ---- the symbolic state at the cut ---- *)
Lemma s1_init : forall b0 b1 b2 fk e1 k1,
  Z.testbit mask 0 = b0 -> Z.testbit mask 1 = b1 -> Z.testbit mask 2 = b2 ->
  aview rsegs (w_H W1) mem1 (SHADOW_OFF + 0x42a5) = Some k1 -> 0 <= k1 < 256 ->
  sv_denot (Ereg regs1 (s1_extra FA k1)) e1 = Z_to_bv 64 k1 ->
  af_lo fk <= k1 <= af_hi fk -> af_al2 fk = 0 ->
  st_ok rsegs (Ereg regs1 (s1_extra FA k1)) (s1_ss b0 b1 b2 fk e1)
    (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 CC_PC1) mem1 (seg_rom rsegs))).
Proof.
intros b0 b1 b2 fk e1 k1 Hb0 Hb1 Hb2 Hav Hk1 He1 Hfk1 Hfk2.
destruct s1_unpack as (_ & _ & _ & _ & _ & _ & HF0 & HF1 & Hal & Happ & Hpres & Hspres & Hfsh & Hmask & Hs0 & Hs1 & _).
destruct s1_regs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G22 & G25 & _ & _ & _ & _ & _ & _ & _ & G23 & _).
pose proof asan_consts as (HC & _).
assert (HFb : 0 <= FA < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (HSb : 0 <= shadow_addr FA < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (HOb : 0 <= SHADOW_OFF < 2 ^ 64)
  by (unfold SHADOW_OFF; change (2 ^ 64) with 18446744073709551616; lia).
assert (E33 : ew (Ereg regs1 (s1_extra FA k1)) 33 = Z_to_bv 64 FA) by (apply s1_ew33).
assert (E23 : ew (Ereg regs1 (s1_extra FA k1)) 23 = Z_to_bv 64 (shadow_addr FA))
  by (rewrite (s1_ewr regs1 FA k1 23 (23%bv : bv 5) ltac:(vm_compute; reflexivity)); exact G23).
assert (E25 : ew (Ereg regs1 (s1_extra FA k1)) 25 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (s1_ewr regs1 FA k1 25 (25%bv : bv 5) ltac:(vm_compute; reflexivity)); exact G25).
assert (E22 : ew (Ereg regs1 (s1_extra FA k1)) 22 = Z_to_bv 64 mask)
  by (rewrite (s1_ewr regs1 FA k1 22 (22%bv : bv 5) ltac:(vm_compute; reflexivity)); exact G22).
assert (E32 : ew (Ereg regs1 (s1_extra FA k1)) 32 = Z_to_bv 64 k1) by (apply s1_ew32).
assert (U33 : bv_unsigned (ew (Ereg regs1 (s1_extra FA k1)) 33) = FA)
  by (rewrite E33; apply unsigned_lit_small; exact HFb).
assert (U23 : bv_unsigned (ew (Ereg regs1 (s1_extra FA k1)) 23) = shadow_addr FA)
  by (rewrite E23; apply unsigned_lit_small; exact HSb).
assert (U25 : bv_unsigned (ew (Ereg regs1 (s1_extra FA k1)) 25) = SHADOW_OFF)
  by (rewrite E25; apply unsigned_lit_small; exact HOb).
rewrite restrict_mkst_fx.
apply (entry_st_ok_full rsegs CC_PC1 s1_sr regs1 (s1_extra FA k1)).
- apply s1_regsok.
- vm_compute; reflexivity.
- apply Forall_cons;
  [ | apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_nil ]]]].
  + apply (rtmb_rw_region rsegs _ (w_H W1) mem1 33%nat FA 32 120 32 120 []);
    [ exact U33 | lia | change (2 ^ 64) with 18446744073709551616; lia
    | intros o Ho; apply Hpres; lia | apply Forall_nil ].
  + apply (rtmb_rw_region rsegs _ (w_H W1) mem1 23%nat (shadow_addr FA)
      0 32 14 15 (rtmb_fsh_cs s1_fsh_pat));
    [ exact U23 | lia | change (2 ^ 64) with 18446744073709551616; lia
    | intros o Ho; apply Hspres; lia | ].
    apply (rtmb_fsh_chunks rsegs _ (w_H W1) mem1 _ s1_fsh_pat Hfsh).
    exact s1_fsh_bytes.
  + apply (rtmb_ro_region rsegs _ (w_H W1) mem1 25%nat SHADOW_OFF 0x42a4 (0x42a4 + 2));
    [ exact U25 | unfold SHADOW_OFF; lia
    | unfold SHADOW_OFF; change (2 ^ 64) with 18446744073709551616; lia | ].
    apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_nil ] ].
    * apply (chunk_ok_val rsegs _ _ SHADOW_OFF 0x42a4 1 (SLit 0) 0);
      [ apply bv_eq; vm_compute; reflexivity | cbn; lia | cbn; lia | ].
      exact (proj1 (rtmb_aview_val1 rsegs (w_H W1) mem1 _ 0 s1_sh0)).
    * apply (chunk_ok_val rsegs _ _ SHADOW_OFF (0x42a4 + 1) 1 e1 k1);
      [ exact He1 | cbn; lia | cbn; lia | ].
      replace (SHADOW_OFF + (0x42a4 + 1)) with (SHADOW_OFF + 0x42a5) by lia.
      exact (proj1 (rtmb_aview_val1 rsegs (w_H W1) mem1 _ k1 Hav)).
  + unfold region_ok, s1_rcl.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold CC_TCL; lia|].
    split; [unfold CC_TCL; change (2 ^ 64) with 18446744073709551616; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_nil ]]].
    * apply (chunk_ok_val rsegs _ _ 0 CC_TCL 4 (SLit 44100) 44100);
      [ apply bv_eq; vm_compute; reflexivity | cbn; lia | cbn; lia | ].
      replace (0 + CC_TCL) with (CC_TCL + 4 * 0) by lia.
      rewrite (ltac:(vm_compute; reflexivity) : (44100 = nth (Z.to_nat 0) RateCfg.closed_list 0)).
      exact (s1_tabvals 0 ltac:(lia)).
    * apply (chunk_ok_val rsegs _ _ 0 (CC_TCL + 4) 4 (SLit 48000) 48000);
      [ apply bv_eq; vm_compute; reflexivity | cbn; lia | cbn; lia | ].
      replace (0 + (CC_TCL + 4)) with (CC_TCL + 4 * 1) by lia.
      rewrite (ltac:(vm_compute; reflexivity) : (48000 = nth (Z.to_nat 1) RateCfg.closed_list 0)).
      exact (s1_tabvals 1 ltac:(lia)).
    * apply (chunk_ok_val rsegs _ _ 0 (CC_TCL + 8) 4 (SLit 96000) 96000);
      [ apply bv_eq; vm_compute; reflexivity | cbn; lia | cbn; lia | ].
      replace (0 + (CC_TCL + 8)) with (CC_TCL + 4 * 2) by lia.
      rewrite (ltac:(vm_compute; reflexivity) : (96000 = nth (Z.to_nat 2) RateCfg.closed_list 0)).
      exact (s1_tabvals 2 ltac:(lia)).
- destruct s1_disj as (P1 & P2 & P3 & P4 & P5 & P6).
  assert (V33 : base_val (Ereg regs1 (s1_extra FA k1)) (Some 33%nat) = FA)
    by (cbn [base_val]; exact U33).
  assert (V23 : base_val (Ereg regs1 (s1_extra FA k1)) (Some 23%nat) = shadow_addr FA)
    by (cbn [base_val]; exact U23).
  assert (V25 : base_val (Ereg regs1 (s1_extra FA k1)) (Some 25%nat) = SHADOW_OFF)
    by (cbn [base_val]; exact U25).
  unfold s1_mem, s1_rframe, s1_rfsh, s1_rclsh, s1_rcl.
  cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite !V33, !V23, !V25. cbn [base_val].
  repeat split; try exact I; assumption.
- unfold facts_ok, s1_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [split; [|split; [|exact I]] | split; [|split; [|exact I]]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33.
    change (2 ^ 5) with 32. split; [split; [lia | change (2 ^ 47) with 140737488355328; lia]|].
    split; [exact Hal | lia].
  + unfold afact_ok. rewrite E32, unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616; lia).
    rewrite Hfk2. change (2 ^ 0) with 1. split; [exact Hfk1 | split; [apply Z.mod_1_r | lia]].
  + assert (Hden : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 22 0) = Z_to_bv 64 mask)
      by (apply (rtsb_den_atom _ 22 mask E22); change (2 ^ 64) with 18446744073709551616; lia).
    assert (A0 : sv_denot (Ereg regs1 (s1_extra FA k1)) (s1_ebit 0) = Z_to_bv 64 (if b0 then 1 else 0))
      by (unfold s1_ebit; rewrite (ccsv_bit_sv _ (SOff 22 0) mask 0 ltac:(lia) Hden), Hb0; reflexivity).
    assert (A1 : sv_denot (Ereg regs1 (s1_extra FA k1)) (s1_ebit 1) = Z_to_bv 64 (if b1 then 1 else 0))
      by (unfold s1_ebit; rewrite (ccsv_bit_sv _ (SOff 22 0) mask 1 ltac:(lia) Hden), Hb1; reflexivity).
    assert (A2 : sv_denot (Ereg regs1 (s1_extra FA k1)) (s1_ebit 2) = Z_to_bv 64 (if b2 then 1 else 0))
      by (unfold s1_ebit; rewrite (ccsv_bit_sv _ (SOff 22 0) mask 2 ltac:(lia) Hden), Hb2; reflexivity).
    unfold s1_conds, s1_bc. cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite A0, A1, A2.
    destruct b0, b1, b2; repeat split; vm_compute; reflexivity.
  + unfold s1_alias.
    exact (shadow_decl_ok _ 33 25 23 FA SHADOW_OFF E33 HFb E25 E23).
Qed.

(* ---- the write rights of the pass: the frame's objects and the frame's shadow ---- *)
Lemma s1_awr : forall k1 e1,
  awr_ok (Ereg regs1 (s1_extra FA k1)) (s1_mem e1) STK sp0 FP (ablocks B ly Sj) (ablocks B lyc S1) lyc
    ((CC_CID, fpos) :: own).
Proof.
intros k1 e1.
destruct s1_unpack as (_ & _ & _ & _ & _ & _ & HF0 & HF1 & Hal & _ & _ & _ & _ & _ & Hs0 & Hs1 & _).
destruct s1_regs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G23 & _).
pose proof asan_consts as (HC & _).
assert (HFb : 0 <= FA < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (HSb : 0 <= shadow_addr FA < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (U33 : bv_unsigned (ew (Ereg regs1 (s1_extra FA k1)) 33) = FA)
  by (rewrite s1_ew33; apply unsigned_lit_small; exact HFb).
assert (U23 : bv_unsigned (ew (Ereg regs1 (s1_extra FA k1)) 23) = shadow_addr FA)
  by (rewrite (s1_ewr regs1 FA k1 23 (23%bv : bv 5) ltac:(vm_compute; reflexivity)), G23;
      apply unsigned_lit_small; exact HSb).
unfold s1_mem.
apply (rck_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 33%nat CC_CID fpos 0);
  [ reflexivity | rewrite U33; lia | left; reflexivity
  | cbn [YP09.r_wlo s1_rframe]; lia
  | change (fs_frame_bytes CC_CID) with 256; cbn [YP09.r_whi s1_rframe]; lia | ].
apply (rck_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 23%nat CC_CID fpos);
  [ reflexivity | exact U23 | left; reflexivity
  | cbn [YP09.r_wlo s1_rfsh]; lia
  | cbn [YP09.r_whi s1_rfsh]; change (fs_frame_bytes CC_CID) with 256;
    change (256 / 8) with 32; lia | ].
apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo s1_rclsh]; lia|].
apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo s1_rcl]; lia|].
apply awr_ok_nil.
Qed.

(* ---- the state the run ends in is the cut 0x83a90 ---- *)
Lemma s1_post : forall k1 e1 (L : list Z) ss' ms2 mat2,
  RateCsv.csv_list mask = L -> Z.of_nat (length L) <= 17 -> s1_final_ok ss' L = true ->
  st_ok rsegs (Ereg regs1 (s1_extra FA k1)) ss' (restrict (w_H W1) ms2) ->
  ajournal rsegs B STK sp0 FP ly Sj W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 (ms_mem ms2)
    (with_vm_backing (m_vm_lazy md1) mat2 md1) k ->
  frame_of (Ereg regs1 (s1_extra FA k1)) (s1_mem e1) (mrestrict (w_H W1) mem1)
    (mrestrict (w_H W1) (ms_mem ms2)) ->
  SRr rsegs W1 (mkCfg ms2 (with_vm_backing (m_vm_lazy md1) mat2 md1))
    (fun W2 c2 => exists S2 regs2 mem2 md2, c2 = cfg_at rsegs CC_PC2 regs2 mem2 md2 /\
      cc_st2 B MT STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos
        S2 W2 regs2 mem2 md2).
Proof.
intros k1 e1 L ss' ms2 mat2 HL Hlen Hok HS2 HJ2 HFr.
pose proof asan_consts as (HC & _).
destruct s1_unpack as (_ & _ & _ & _ & _ & _ & HF0 & HF1 & Hal & Happ & _ & _ & _ & _ & Hs0 & Hs1 & Hsep
  & Hsa & Hsb & Hsc & Hsd & _ & _ & Hsp16).
change (2 ^ 47) with 140737488355328 in Hsb.
destruct s1_regs as (G2 & G9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G25 & _ & _ & _ & _ & _ & _ & _ & G23 & G24).
destruct H1 as (HP & HFR & _).
assert (HFb : 0 <= FA < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (HSb : 0 <= shadow_addr FA < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (HOb : 0 <= SHADOW_OFF < 2 ^ 64)
  by (unfold SHADOW_OFF; change (2 ^ 64) with 18446744073709551616; lia).
assert (E33 : ew (Ereg regs1 (s1_extra FA k1)) 33 = Z_to_bv 64 FA) by (apply s1_ew33).
assert (E23 : ew (Ereg regs1 (s1_extra FA k1)) 23 = Z_to_bv 64 (shadow_addr FA))
  by (rewrite (s1_ewr regs1 FA k1 23 (23%bv : bv 5) ltac:(vm_compute; reflexivity)); exact G23).
assert (E25 : ew (Ereg regs1 (s1_extra FA k1)) 25 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (s1_ewr regs1 FA k1 25 (25%bv : bv 5) ltac:(vm_compute; reflexivity)); exact G25).
assert (V33 : base_val (Ereg regs1 (s1_extra FA k1)) (Some 33%nat) = FA)
  by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; exact HFb).
assert (V23 : base_val (Ereg regs1 (s1_extra FA k1)) (Some 23%nat) = shadow_addr FA)
  by (cbn [base_val]; rewrite E23; apply unsigned_lit_small; exact HSb).
assert (V25 : base_val (Ereg regs1 (s1_extra FA k1)) (Some 25%nat) = SHADOW_OFF)
  by (cbn [base_val]; rewrite E25; apply unsigned_lit_small; exact HOb).
(* the bytes the pass did not write read as they did at the cut *)
assert (Hkept : forall a, 0 <= a < 2 ^ 64 ->
  ~ (FA + 32 <= a < FA + 120) -> a <> shadow_addr FA + 14 ->
  aview rsegs (w_H W1) (ms_mem ms2) a = aview rsegs (w_H W1) mem1 a).
{ intros a Ha Hw1 Hw2. unfold aview, mbyte.
  rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr). rewrite unsigned_lit_small in Hr by exact Ha.
  unfold s1_mem in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi s1_rframe s1_rfsh s1_rclsh s1_rcl] in Hr;
    rewrite ?V33, ?V23, ?V25 in Hr; lia. }
assert (Hne : forall a, FA <= a < FA + 256 -> a <> shadow_addr FA + 14)
  by (destruct Hsep as [Hd|Hd]; intros a Ha; lia).
assert (Hhi : forall a, alloc_ceiling <= a -> a <= sp0 ->
  aview rsegs (w_H W1) (ms_mem ms2) a = aview rsegs (w_H W1) mem1 a).
{ intros a Ha1 Ha2. apply Hkept; [change (2 ^ 64) with 18446744073709551616; lia | lia | lia]. }
(* the run's final state *)
apply andb_prop in Hok as [Hok Hm1]. apply andb_prop in Hok as [Hok Hm0].
apply andb_prop in Hok as [Hok H28]. apply andb_prop in Hok as [Hok H24].
apply andb_prop in Hok as [Hok Hrg]. apply andb_prop in Hok as [Hpc Hrv].
apply Z.eqb_eq in Hpc.
apply andb_prop in Hrg as [Hrg Q25]. apply andb_prop in Hrg as [Hrg Q23].
apply andb_prop in Hrg as [Hrg Q9]. apply andb_prop in Hrg as [Hrg Q8].
apply andb_prop in Hrg as [Hrg Q4]. apply andb_prop in Hrg as [Q2 Q3].
assert (Hkp : forall (r : bv 5) (m : nat), sv_eqb (sr_get (ss_regs ss') r) (SOff m 0) = true ->
  Z.of_nat m = bv_unsigned r -> getr (ms_regs ms2) r = getr regs1 r).
{ intros r m Hq Hm. rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms2 r HS2).
  apply sv_eqb_eq in Hq. rewrite Hq.
  rewrite (rtsb_den_atom _ m (bv_unsigned (getr regs1 r))
    ltac:(rewrite (s1_ewr regs1 FA k1 m r Hm); symmetry; apply Z_to_bv_bv_unsigned) (u64_range _)).
  apply Z_to_bv_bv_unsigned. }
assert (K2 : getr (ms_regs ms2) 2 = getr regs1 2) by (apply (Hkp _ 2%nat Q2); vm_compute; reflexivity).
assert (K3 : getr (ms_regs ms2) 3 = getr regs1 3) by (apply (Hkp _ 3%nat Q3); vm_compute; reflexivity).
assert (K4 : getr (ms_regs ms2) 4 = getr regs1 4) by (apply (Hkp _ 4%nat Q4); vm_compute; reflexivity).
assert (K8 : getr (ms_regs ms2) 8 = getr regs1 8) by (apply (Hkp _ 8%nat Q8); vm_compute; reflexivity).
assert (K9 : getr (ms_regs ms2) 9 = getr regs1 9) by (apply (Hkp _ 9%nat Q9); vm_compute; reflexivity).
assert (K23 : getr (ms_regs ms2) 23 = getr regs1 23) by (apply (Hkp _ 23%nat Q23); vm_compute; reflexivity).
assert (K25 : getr (ms_regs ms2) 25 = getr regs1 25) by (apply (Hkp _ 25%nat Q25); vm_compute; reflexivity).
assert (K24 : getr (ms_regs ms2) 24 = w64 (FA + 32)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms2 (24%bv : bv 5) HS2).
  apply sv_eqb_eq in H24. rewrite H24.
  exact (s1_den_off _ 33 _ 32 E33 HFb ltac:(change (2 ^ 64) with 18446744073709551616; lia)). }
assert (K28 : getr (ms_regs ms2) 28 = w64 (Z.of_nat (length (RateCsv.csv_list mask)))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W1) _ _ ms2 (28%bv : bv 5) HS2).
  apply sv_eqb_eq in H28. rewrite H28, HL.
  apply s1_den_lit. change (2 ^ 64) with 18446744073709551616. lia. }
(* the bytes of want and the frame's shadow, from the final state's two regions *)
destruct (nth_error (ss_mem ss') 0) as [r0|] eqn:E0; [|discriminate Hm0].
destruct (nth_error (ss_mem ss') 1) as [r1|] eqn:E1; [|discriminate Hm1].
apply andb_prop in Hm0 as [Hb0 Hc0]. apply andb_prop in Hm1 as [Hb1 Hc1].
apply obase_eqb_eq in Hb0. apply obase_eqb_eq in Hb1.
pose proof (s1_chk_bytes_ok _ _ r0 32 L (rtsb_region_nth _ _ ms2 0 r0 (w_H W1) HS2 E0) Hc0) as Hby0.
pose proof (s1_chk_bytes_ok _ _ r1 0 s1_fsh_pat (rtsb_region_nth _ _ ms2 1 r1 (w_H W1) HS2 E1) Hc1) as Hby1.
rewrite Hb0, V33 in Hby0. rewrite Hb1, V23 in Hby1.
(* the configuration *)
apply SRr_ret.
exists S1, (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy md1) mat2 md1).
split.
{ unfold cfg_at. rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ ss' ms2 HS2
    ltac:(destruct (ss_resv ss'); [discriminate Hrv | reflexivity])) at 1.
  rewrite Hpc. reflexivity. }
split; [exact HP|].
split.
{ destruct HFR as (_ & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & _ & _ & _ & _
    & F17 & F18 & F19 & F20 & F21 & F22 & F23 & N3 & N4 & N8 & N9 & N23 & N24).
  split; [exact HJ2|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
  split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; [exact F10|].
  split; [eapply same_io_trans; [exact F11 | apply same_io_wvb]|].
  split.
  { intros a Ha Hstk Hown. rewrite Hkept; [exact (F12 a Ha Hstk Hown) | exact Ha | |].
    - intros Hc. apply Hown. apply (s1_own_obj a). lia.
    - intros Hc. apply Hown. apply (s1_own_sh a). lia. }
  split; [exact HF0|]. split; [exact HF1|]. split; [exact Happ|]. split; [exact Hal|].
  split.
  { rewrite (rdword_ext (aview rsegs (w_H W1) mem1) (aview rsegs (w_H W1) (ms_mem ms2)) (FA + 248)
      ltac:(intros i Hi; apply Hkept; [lia | lia | apply Hne; lia])). exact F17. }
  split.
  { intros j Hj. assert (Hjz : 0 <= Z.of_nat j <= 12) by lia.
    rewrite (rdword_ext (aview rsegs (w_H W1) mem1) (aview rsegs (w_H W1) (ms_mem ms2))
      (spZ regs - 8 - 8 * Z.of_nat j)
      ltac:(intros i Hi; apply Hhi; unfold T_csv_STK_B, ESTACK in *; lia)). exact (F18 j Hj). }
  destruct (cc_rbase_bounds (spZ regs) Hsp16) as [_ [Hrb1 Hrb2]].
  split.
  { rewrite (rdword_ext (aview rsegs (w_H W1) mem1) (aview rsegs (w_H W1) (ms_mem ms2))
      (cc_rbase (spZ regs) + 24)
      ltac:(intros i Hi; apply Hhi; unfold T_csv_STK_B, ESTACK, CC_FRAME in *; lia)). exact F19. }
  split.
  { rewrite (rdword_ext (aview rsegs (w_H W1) mem1) (aview rsegs (w_H W1) (ms_mem ms2))
      (cc_rbase (spZ regs) + 32)
      ltac:(intros i Hi; apply Hhi; unfold T_csv_STK_B, ESTACK, CC_FRAME in *; lia)). exact F20. }
  split.
  { rewrite (rdword_ext (aview rsegs (w_H W1) mem1) (aview rsegs (w_H W1) (ms_mem ms2))
      (cc_rbase (spZ regs) + 40)
      ltac:(intros i Hi; apply Hhi; unfold T_csv_STK_B, ESTACK, CC_FRAME in *; lia)). exact F21. }
  split.
  { rewrite (rdword_ext (aview rsegs (w_H W1) mem1) (aview rsegs (w_H W1) (ms_mem ms2))
      (cc_rbase (spZ regs) + 48)
      ltac:(intros i Hi; apply Hhi; unfold T_csv_STK_B, ESTACK, CC_FRAME in *; lia)). exact F22. }
  split.
  { rewrite (rdword_ext (aview rsegs (w_H W1) mem1) (aview rsegs (w_H W1) (ms_mem ms2))
      (cc_rbase (spZ regs) + 56)
      ltac:(intros i Hi; apply Hhi; unfold T_csv_STK_B, ESTACK, CC_FRAME in *; lia)). exact F23. }
  split; [rewrite K3; exact N3|]. split; [rewrite K4; exact N4|]. split; [rewrite K8; exact N8|].
  split; [rewrite K9; exact N9|]. split; [rewrite K23; exact N23 | exact K24]. }
split.
{ change (CC_SH_A ++ repeat 0 12) with s1_fsh_pat.
  intros i Hi. rewrite (ltac:(vm_compute; reflexivity) : Z.of_nat (length s1_fsh_pat) = 32) in Hi.
  unfold aview.
  replace (shadow_addr FA + i) with (shadow_addr FA + 0 + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (Hby1 (Z.to_nat i) ltac:(rewrite (ltac:(vm_compute; reflexivity) : length s1_fsh_pat = 32%nat); lia)).
  cbn [option_map]. f_equal. rewrite rtmb_unsigned_byte. apply Z.mod_small.
  apply (proj1 (Forall_forall _ _) s1_fsh_bytes). apply nth_In.
  rewrite (ltac:(vm_compute; reflexivity) : length s1_fsh_pat = 32%nat). lia. }
split.
{ rewrite HL. intros j Hj. unfold RateCsv.csv_bytes in *. rewrite length_map in Hj.
  rewrite nth_error_map, (nth_error_nth' L 0 Hj). cbn [option_map].
  exact (Hby0 j Hj). }
split; [rewrite K2; exact G2|]. split; [rewrite K25; exact G25 | exact K28].
Qed.

(* ---- what the segment must prove ---- *)
Definition s1_Q : world rsegs -> config -> Prop :=
  fun W2 c2 => exists S2 regs2 mem2 md2, c2 = cfg_at rsegs CC_PC2 regs2 mem2 md2 /\
    cc_st2 B MT STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos
      S2 W2 regs2 mem2 md2.

(* ---- one run of the shadow-aware engine, from 0x83948 to 0x83a90 ---- *)
Lemma s1_run : forall b0 b1 b2 fk e1 k1 L,
  Z.testbit mask 0 = b0 -> Z.testbit mask 1 = b1 -> Z.testbit mask 2 = b2 ->
  aview rsegs (w_H W1) mem1 (SHADOW_OFF + 0x42a5) = Some k1 -> 0 <= k1 < 256 ->
  sv_denot (Ereg regs1 (s1_extra FA k1)) e1 = Z_to_bv 64 k1 ->
  af_lo fk <= k1 <= af_hi fk -> af_al2 fk = 0 ->
  RateCsv.csv_list mask = L -> Z.of_nat (length L) <= 17 ->
  (let r := sym_run_toN_sh rsegs s1_tbl FUEL CC_PC2 (s1_ss b0 b1 b2 fk e1) in
   s1_final_ok (fst r) L = true /\ match snd r with RS_ecall => False | _ => True end) ->
  SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
intros b0 b1 b2 fk e1 k1 L Hb0 Hb1 Hb2 Hav Hk1 He1 Hf1 Hf2 HL Hlen Hrun.
cbv zeta in Hrun. destruct Hrun as [Hok Hst].
destruct s1_unpack as (HJ & _).
unfold cfg_at.
eapply (rck_run_to_sh_AJ B LAWS s1_tbl s1_tbl_ok W1 FUEL CC_PC2 (Ereg regs1 (s1_extra FA k1))
  (s1_ss b0 b1 b2 fk e1) _ _ (mkst regs1 (w64 CC_PC1) mem1 (seg_rom rsegs))).
- exact (s1_init b0 b1 b2 fk e1 k1 Hb0 Hb1 Hb2 Hav Hk1 He1 Hf1 Hf2).
- exact (surjective_pairing _).
- exact Hst.
- exact HJ.
- apply s1_awr.
- unfold run_post_AJ. intros ms2 mat2 HS2 HJ2 HF HFr HG.
  exact (s1_post k1 e1 L _ ms2 mat2 HL Hlen Hok HS2 HJ2 HFr).
Qed.

(* ---- the eight values of mask mod 8; the four with bit 2 set split once more on the shadow byte of
       closed_list's second granule, which the contract leaves undecided (0, or in [4, 8)) ---- *)
Lemma s1_c0 : mask mod 8 = 0 -> SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
intros Hm8. destruct s1_unpack as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hmask&_).
destruct (ccsv_case0 mask ltac:(lia) Hm8) as (T0 & T1 & T2 & _ & _ & TL & _ & _ & _).
destruct s1_sh1 as (k1 & Hav & Hk1c & Hk1r).
assert (Hden : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 32 0) = Z_to_bv 64 k1)
  by (apply (rtsb_den_atom _ 32 k1 (s1_ew32 regs1 FA k1)); change (2 ^ 64) with 18446744073709551616; lia).
apply (s1_run false false false (mkAF 0 255 0) (SOff 32 0) k1 _ T0 T1 T2 Hav Hk1r Hden
  ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
vm_compute. split; [reflexivity | exact I].
Qed.

Lemma s1_c1 : mask mod 8 = 1 -> SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
intros Hm8. destruct s1_unpack as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hmask&_).
destruct (ccsv_case1 mask ltac:(lia) Hm8) as (T0 & T1 & T2 & _ & _ & TL & _ & _ & _).
destruct s1_sh1 as (k1 & Hav & Hk1c & Hk1r).
assert (Hden : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 32 0) = Z_to_bv 64 k1)
  by (apply (rtsb_den_atom _ 32 k1 (s1_ew32 regs1 FA k1)); change (2 ^ 64) with 18446744073709551616; lia).
apply (s1_run true false false (mkAF 0 255 0) (SOff 32 0) k1 _ T0 T1 T2 Hav Hk1r Hden
  ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
vm_compute. split; [reflexivity | exact I].
Qed.

Lemma s1_c2 : mask mod 8 = 2 -> SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
intros Hm8. destruct s1_unpack as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hmask&_).
destruct (ccsv_case2 mask ltac:(lia) Hm8) as (T0 & T1 & T2 & _ & _ & TL & _ & _ & _).
destruct s1_sh1 as (k1 & Hav & Hk1c & Hk1r).
assert (Hden : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 32 0) = Z_to_bv 64 k1)
  by (apply (rtsb_den_atom _ 32 k1 (s1_ew32 regs1 FA k1)); change (2 ^ 64) with 18446744073709551616; lia).
apply (s1_run false true false (mkAF 0 255 0) (SOff 32 0) k1 _ T0 T1 T2 Hav Hk1r Hden
  ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
vm_compute. split; [reflexivity | exact I].
Qed.

Lemma s1_c3 : mask mod 8 = 3 -> SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
intros Hm8. destruct s1_unpack as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hmask&_).
destruct (ccsv_case3 mask ltac:(lia) Hm8) as (T0 & T1 & T2 & _ & _ & TL & _ & _ & _).
destruct s1_sh1 as (k1 & Hav & Hk1c & Hk1r).
assert (Hden : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 32 0) = Z_to_bv 64 k1)
  by (apply (rtsb_den_atom _ 32 k1 (s1_ew32 regs1 FA k1)); change (2 ^ 64) with 18446744073709551616; lia).
apply (s1_run true true false (mkAF 0 255 0) (SOff 32 0) k1 _ T0 T1 T2 Hav Hk1r Hden
  ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
vm_compute. split; [reflexivity | exact I].
Qed.

Lemma s1_c4 : mask mod 8 = 4 -> SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
intros Hm8. destruct s1_unpack as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hmask&_).
destruct (ccsv_case4 mask ltac:(lia) Hm8) as (T0 & T1 & T2 & _ & _ & TL & _ & _ & _).
destruct s1_sh1 as (k1 & Hav & Hk1c & Hk1r).
destruct Hk1c as [Hk0|Hk0].
- subst k1.
  apply (s1_run false false true (mkAF 0 0 0) (SLit 0) 0 _ T0 T1 T2 Hav ltac:(lia)
    ltac:(apply s1_den_lit; change (2 ^ 64) with 18446744073709551616; lia)
    ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
  vm_compute. split; [reflexivity | exact I].
- assert (Hden : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 32 0) = Z_to_bv 64 k1)
    by (apply (rtsb_den_atom _ 32 k1 (s1_ew32 regs1 FA k1)); change (2 ^ 64) with 18446744073709551616; lia).
  apply (s1_run false false true (mkAF 4 7 0) (SOff 32 0) k1 _ T0 T1 T2 Hav Hk1r Hden
    ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
  vm_compute. split; [reflexivity | exact I].
Qed.

Lemma s1_c5 : mask mod 8 = 5 -> SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
intros Hm8. destruct s1_unpack as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hmask&_).
destruct (ccsv_case5 mask ltac:(lia) Hm8) as (T0 & T1 & T2 & _ & _ & TL & _ & _ & _).
destruct s1_sh1 as (k1 & Hav & Hk1c & Hk1r).
destruct Hk1c as [Hk0|Hk0].
- subst k1.
  apply (s1_run true false true (mkAF 0 0 0) (SLit 0) 0 _ T0 T1 T2 Hav ltac:(lia)
    ltac:(apply s1_den_lit; change (2 ^ 64) with 18446744073709551616; lia)
    ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
  vm_compute. split; [reflexivity | exact I].
- assert (Hden : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 32 0) = Z_to_bv 64 k1)
    by (apply (rtsb_den_atom _ 32 k1 (s1_ew32 regs1 FA k1)); change (2 ^ 64) with 18446744073709551616; lia).
  apply (s1_run true false true (mkAF 4 7 0) (SOff 32 0) k1 _ T0 T1 T2 Hav Hk1r Hden
    ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
  vm_compute. split; [reflexivity | exact I].
Qed.

Lemma s1_c6 : mask mod 8 = 6 -> SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
intros Hm8. destruct s1_unpack as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hmask&_).
destruct (ccsv_case6 mask ltac:(lia) Hm8) as (T0 & T1 & T2 & _ & _ & TL & _ & _ & _).
destruct s1_sh1 as (k1 & Hav & Hk1c & Hk1r).
destruct Hk1c as [Hk0|Hk0].
- subst k1.
  apply (s1_run false true true (mkAF 0 0 0) (SLit 0) 0 _ T0 T1 T2 Hav ltac:(lia)
    ltac:(apply s1_den_lit; change (2 ^ 64) with 18446744073709551616; lia)
    ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
  vm_compute. split; [reflexivity | exact I].
- assert (Hden : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 32 0) = Z_to_bv 64 k1)
    by (apply (rtsb_den_atom _ 32 k1 (s1_ew32 regs1 FA k1)); change (2 ^ 64) with 18446744073709551616; lia).
  apply (s1_run false true true (mkAF 4 7 0) (SOff 32 0) k1 _ T0 T1 T2 Hav Hk1r Hden
    ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
  vm_compute. split; [reflexivity | exact I].
Qed.

Lemma s1_c7 : mask mod 8 = 7 -> SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
intros Hm8. destruct s1_unpack as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hmask&_).
destruct (ccsv_case7 mask ltac:(lia) Hm8) as (T0 & T1 & T2 & _ & _ & TL & _ & _ & _).
destruct s1_sh1 as (k1 & Hav & Hk1c & Hk1r).
destruct Hk1c as [Hk0|Hk0].
- subst k1.
  apply (s1_run true true true (mkAF 0 0 0) (SLit 0) 0 _ T0 T1 T2 Hav ltac:(lia)
    ltac:(apply s1_den_lit; change (2 ^ 64) with 18446744073709551616; lia)
    ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
  vm_compute. split; [reflexivity | exact I].
- assert (Hden : sv_denot (Ereg regs1 (s1_extra FA k1)) (SOff 32 0) = Z_to_bv 64 k1)
    by (apply (rtsb_den_atom _ 32 k1 (s1_ew32 regs1 FA k1)); change (2 ^ 64) with 18446744073709551616; lia).
  apply (s1_run true true true (mkAF 4 7 0) (SOff 32 0) k1 _ T0 T1 T2 Hav Hk1r Hden
    ltac:(cbn [af_lo af_hi]; lia) eq_refl TL ltac:(cbn [length]; lia)).
  vm_compute. split; [reflexivity | exact I].
Qed.

Lemma s1_main : SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1) s1_Q.
Proof.
destruct (ccsv_mod8_cases mask) as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
- exact (s1_c0 H). - exact (s1_c1 H). - exact (s1_c2 H). - exact (s1_c3 H).
- exact (s1_c4 H). - exact (s1_c5 H). - exact (s1_c6 H). - exact (s1_c7 H).
Qed.
End w.

(* ======================================== the segment ======================================== *)
Theorem ccsv_S1 : CC_S1_stmt B MT.
Proof.
unfold CC_S1_stmt.
intros STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 HH.
exact (s1_main STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos
  S1 W1 regs1 mem1 md1 HH).
Qed.
End s.

About ccsv_S1.
Print Assumptions ccsv_S1.
