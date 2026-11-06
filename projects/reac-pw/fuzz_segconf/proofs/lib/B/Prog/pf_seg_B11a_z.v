(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 386 of its 431 lines of code are new or changed and 408 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B10a_s.v, with its module paths, module names, addresses and numbers changed; 404 of its 485 lines of code are new or changed and 350 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the ZST piece of
   segment B11a of reac_segconf_parse_file's walk and its call of reac_box_catalogue_by_token,
     b11_zst_ok : forall fx n, B11_RBT_stmt n -> forall li, B11_ZST_stmt n li      (lib/B/Prog/pf_seg_B11a_k.v)
   The B11a segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, B11a's ZST cut and the by_token call).
   ADAPTED from a working branch + U piece walks; templates the B10a segment lane's pf_seg_B10a_s.v (the EXIT
   seed b10_ss3 / b10_entry3) and pf_seg_B10a_x.v (the token run with one written byte, its check covered by a
   shadow entry, the byte read back), the B11a segment lane's pf_seg_B11a_m.v (a region read back, b11_kept, the cut
   rebuilt with the kit's move lemmas), the B9 segment lane's pf_seg_B9_s11.v (a program callee through PaCall's call rule
   at sp = s1) and pf_seg_B9_c.v (b9_addr_cells: a frame range addressable from pf_fsh), the B7 segment lane's
   pf_seg_B7_ch.v (b7_chain, the frame chain at a call made at s1), and the released fuzz_command walk
   check_reply_s2.v (cl_callS to a program callee).

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), ZST 0x889ac .. the call 0x889d8, 12 instructions
   (the check's slow arm 0x8901c-0x89024 and its error call 0x892a0 are not reached):
     0x889ac ld a0,16(s1)        a0 = slot 0x10 = pf_nt (F + 0x2e0), the 64-bit `not` of model low
     0x889b0 bltu a0,a3,0x891c8  UBSan trap T21 (model low + li wraps): NOT taken
     0x889b4 ld a1,144(s1)       a1 = slot 0x90 = model low = F + 0x2e0
     0x889b8 add a0,a1,a3        a0 = low + li
     0x889bc mv a3,a1
     0x889c0 .. 0x889cc          check B#26 (store1 at low + li): srli / add s4 / lb / bnez -> 0x8901c
     0x889d0 sb zero,0(a0)       the NUL of the folded value: low[li] = 0
     0x889d4 mv a0,a3            a0 = low
     0x889d8 jal reac_box_catalogue_by_token     returns at 0x889dc = RBT
   THE WALK.
   - The seed at ZST (b11z_ss, the measured seed of the B11a segment lane's scratch ZzG3Bpb11aX.v with the atoms renamed):
     every register its own atom; a read-only region on s1 (atom 9) with the chunks 0x10 (atom 32, ~low, fact
     [2 ^ 64 - 2 ^ 47, 2 ^ 64 - 4097]) and 0x90 (atom 33, low, fact [4096, 2 ^ 47 - 1]); a one-byte writable region
     on atom 34 = low + li (alias low + a3), fact [4096, 2 ^ 47 - 1]; a3 = li (atom 13, fact [0, 23]); s4 = SB; the
     shadow entry mkSHE 34 0 1, sh_ok by shent_ok_of_range from model low's 24 addressable bytes (b11_ra_frame: its
     cells 0x5c .. 0x5e are 0 under PF_SC_L146).
   - One token run to the call (paj_run_tok, PTS_call SS_reac_box_catalogue_by_token): T21 decided by the range facts
     of atoms 32 and 13 (~low >= 2 ^ 64 - 2 ^ 47 > 23 >= li, from pf_tf's F + 2048 <= 2 ^ 47); check B#26 covered by
     the shadow entry of low + li; `sb zero` writes the region; a0 = low.
   - At the call state: b11_cx carried by b11_cx_move (the run wrote only low + li, inside model low); model low holds
     the folded value r_low val 0 24 and its NUL (b11_low, the byte read back from the region, b11z_nth_low); its
     bytes addressable (b11z_addr_low, from the frame's shadow at PF_SC_L146); the call target pa_sigma
     SS_reac_box_catalogue_by_token is BASE + AF_reac_box_catalogue_by_token (SIGP).
   - The call: PaCall.cl_callS with BYTOKEN at o = s1 - sp0 (16-aligned; 8256 + 368 <= 12832), the frame chain
     b11z_chain (b7_chain's), afn_pre from the journal, by_token_pre (low <> 0, sa_str, sa_addr, sa_loc by the
     class-5 frame, length + 1 < 2 ^ 32, sa_cat), arodata_okP (pf_obj), st_nev (pf_cx); the callee's footprint is [].
   - At the return 0x889dc: b11_cx by b11_cx_move from sa_kept (window [s1 - 8256, s1), inside b11_Wr's stack part;
     the window's bytes stay present by the callee's journal), sa_noalloc and the journal (0 + 0 events); model low's
     string kept (below alloc_ceiling, outside the window); the registers by aregs_preserved; a0 = cat_ptr catA
     (by_token (r_low val 0 24)) from the post. Then the RBT statement.
   CHECKS AND TRAPS: B#26 (covered by mkSHE 34 0 1), T21 (decided by the executor from the seed's range facts).
   SECTION HYPOTHESES: BYTOKEN (reac_box_catalogue_by_token_contract at BASE + AF_reac_box_catalogue_by_token,
   STK_reac_box_catalogue_by_token, RLO_A, RHI_A, catA, at every FP state), SIGP (seg_sig_prog). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  reac_box_catalogue_by_token_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B11a_k pf_seg_B11a_g
  pf_seg_B11a_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_seg_B10a_s.v / pf_seg_B10a_x.v / pf_seg_B11a_m.v / pf_seg_B9_s1.v, renamed) ---------- *)
Lemma b11z_set_fs_id : forall s, set_fs (st_fs s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma b11z_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
(* model low's three shadow cells 0x5c .. 0x5e are 0 while it is in scope *)
Lemma b11z_shb_l146 : forall i, 92 <= i < 95 -> pf_shb PF_SC_L146 i = 0.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (b11z_zrange (fun i => pf_shb PF_SC_L146 i =? 0) 92 3). vm_compute. reflexivity.
Qed.
Lemma b11z_bvr' : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma b11z_u_add : forall E a b x y, U E a = x -> U E b = y -> 0 <= x + y < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Ha Hb H. rewrite U_SAlu, Ha, Hb. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. Qed.
Lemma b11z_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma b11z_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = v -> ew E n = v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma b11z_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma b11z_reg_atom : forall (regs : bvmap 5 word) (r : bv 5) E n c v,
  getr regs r = sv_denot E (SOff n c) -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> getr regs r = w64 (v + c).
Proof. intros regs r E n c v H Hn Hv. rewrite H. exact (b11z_den_off E n v c Hn Hv). Qed.
(* the bytes of the folded value: r_low val 0 24 is map lower (firstn 23 val) (pf_seg_B11a_f.v b11f_low_map) *)
Lemma b11z_nth_low : forall val i, nulfree val -> (i < length (r_low val 0 24))%nat ->
  nth i (r_low val 0 24) 0 = lower (nth i val 0).
Proof.
intros val i H Hi. rewrite (b11f_low_map val 24 H) in *.
rewrite length_map, length_firstn in Hi.
rewrite (nth_indep (map lower (firstn (24 - 1) val)) 0 (lower 0)) by (rewrite length_map, length_firstn; lia).
rewrite map_nth. rewrite b11f_nth_firstn by lia. reflexivity.
Qed.
(* a C string whose bytes, NUL and slack word a reader keeps *)
Lemma b11z_str_keep : forall (rd rd' : reader) p s, sa_str rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 8 -> rd' x = rd x) -> sa_str rd' p s.
Proof.
intros rd rd' p s ((Hz & Hn) & Ht) K.
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite K by lia. exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite K by lia. exact (Ht x Hx).
Qed.
Ltac b11z_in := cbn [In app PF_RL PF_RM PF_SL b11_FI]; repeat first [left; reflexivity | right].
(* a register of the state a run stopped in, as the executor's term (st_ok: the run ended at a call) *)
Ltac b11z_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* the awr obligation of a run whose regions are read-only, but for one written byte at atom nn *)
Ltac b11z_awr1 nn U HFRM :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (first [ apply awr_ok_nil
                | apply awr_ok_cons_ro; [cbn; lia|]
                | eapply awr_ok_cons_gen with (n := nn); [reflexivity | exact U | apply HFRM |] ]).

(* ---------- the seed at ZST (0x889ac) ---------- *)
(* every register its own atom; s1's slots 0x10 (atom 32 = ~low) and 0x90 (atom 33 = low) read only; atom 34 =
   low + li (the alias low + a3) one written byte; a3 = li (atom 13) *)
Definition b11z_Bx : sv := SOff 20 0.
Definition b11z_ss : sstate :=
  mkSS B11_ZST sr_atoms
    [YP09.mkRegion (Some 9%nat) 0x10 0x98 0 0
       [YP09.mkChunk 0x10 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 33 0))];
     YP09.mkRegion (Some 34%nat) 0 1 0 1 []] None
    (mkFacts [(32%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0); (33%nat, mkAF 4096 (2 ^ 47 - 1) 0);
              (34%nat, mkAF 4096 (2 ^ 47 - 1) 0); (13%nat, mkAF 0 23 0); (20%nat, mkAF SB SB 0)] []
       [(SAlu ALU_ADD (SOff 33 0) (SOff 13 0), SOff 34 0)]).
Definition b11z_SH : list shent := [mkSHE 34 0 1].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis BYTOKEN : forall fx0 : YK11.FPState, @reac_box_catalogue_by_token_contract fx0 rc SK SEGS B
  (BASE + AF_reac_box_catalogue_by_token) STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
Hypothesis SIGP : seg_sig_prog (PI := PI).

Definition b11z_E (regs1 : bvmap 5 word) (low k : Z) : env :=
  Eimg (Ereg regs1 [w64 (pf_nt low); w64 low; w64 (low + k)]).

(* reading a one-byte cell of a region the run wrote (pf_seg_B11a_m.v b11m_cell_of_region) *)
Definition b11z_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
Lemma b11z_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> b11z_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od v HR Hb Hc.
apply existsb_exists in Hc as (c & Hin & Hc).
destruct c as [o [w e | | | ]]; cbn [YP09.c_val YP09.c_off] in Hc; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hc as [Hc Hv]. apply andb_prop in Hc as [Ho Hw].
apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hv. subst o w.
unfold region_ok in HR. cbv zeta in HR. cbn [YP09.r_base YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb, Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. cbn [option_map]. rewrite Hv. reflexivity.
Qed.

(* a range of model low (F + 0x2e0, 24 bytes) is addressable, with its 8-byte shadow hull inside the frame's 144
   cells, while model low is in scope (pf_seg_B9_c.v b9_addr_cells at cells 0x5c .. 0x5e) *)
Lemma b11z_addr_low : forall v pos (rd : reader) q n, b11_G v pos -> pf_fsh rd (pf_SH v pos) PF_SC_L146 ->
  pf_F v pos + 736 <= q -> 0 <= n -> q + n <= pf_F v pos + 760 -> sa_addr rd q n.
Proof.
intros v pos rd q n GG HFSH Hq Hn Hqn.
pose proof GG as (_ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
destruct (b11_SHb v pos GG) as (ESH & SH1 & SH2 & F8).
pose proof alloc_ceiling_lt as HC.
assert (HF8 : pf_F v pos mod 8 = 0) by (rewrite F8, Z.mul_comm; apply Z_mod_mult).
assert (EA : forall x, shadow_of_addr SHADOW_OFF x = pf_SH v pos + (x - pf_F v pos) / 8).
{ intros x. replace x with (pf_F v pos + (x - pf_F v pos)) at 1 by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8). reflexivity. }
split; [lia|]. split; [lia|].
split; [apply amem_range_high; [lia | destruct F4; [left | right]; lia | lia]|].
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  rewrite EA.
  assert (Hi : 92 <= (x - pf_F v pos) / 8 < 95)
    by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  rewrite (HFSH ((x - pf_F v pos) / 8)) by lia. rewrite b11z_shb_l146 by exact Hi. reflexivity.
- intros Hn0 s Hs.
  change (shadow_addr q) with (shadow_of_addr SHADOW_OFF q) in Hs.
  change (shadow_addr (q + n - 1)) with (shadow_of_addr SHADOW_OFF (q + n - 1)) in Hs.
  rewrite !EA in Hs.
  assert (B1 : 92 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 95) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (HFSH (s - pf_SH v pos)) by lia. discriminate.
Qed.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run (fx := fx) B LAWS.

(* THE FRAME CHAIN AT A CALL MADE AT s1: the prologue's record (ra at sp0 - 8, the entry s0 at sp0 - 16) pushed on
   afn_pre's chain, which the journal keeps above sp0 (pf_seg_B7_ch.v b7_chain, with b11_geo's numbers) *)
Lemma b11z_chain : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (pf_sp0 v) ch1.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc HB.
pose proof (b11_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (GG & _).
pose proof GG as (G1 & G2 & G3 & G4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & GC & _).
pose proof HB as (HCX & HFI & _).
destruct HFI as (HJ & Hly & _ & _ & HSV & _).
destruct HCX as (HPRE & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & _ & _ & _ & Hshi & H47' & _ & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
subst lyc.
pose proof STK_values as (_ & _ & _ & SPF & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *.
destruct (Z_lt_le_dec (pf_sp0 v) (ly_top (p_ly v) - 16)) as [Hlt | Hge].
- exists ((pf_sp0 v, raZ (p_regs v), s0Z (p_regs v)) :: p_ch v).
  apply (achain_push (p_ly v) (rdW (p_W v) (p_mem v)) (rdW Wc memc) (pf_sp0 v) (s0Z (p_regs v)) (raZ (p_regs v))
    (p_ch v) (pf_s1 v) Hch).
  + lia.
  + intros a Ha. apply F1; [lia | rewrite SPF; lia |].
    intros Hf. apply b11_rcw_in in Hf. unfold seg_spec.SEG_C_SIZE in *. lia.
  + assert (E1 : Z_to_bv 5 1 = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 0%nat 1 eq_refl) as H1. rewrite E1 in H1.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 0) with (pf_sp0 v - 8) in H1 by lia. exact H1.
  + assert (E8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 1%nat 8 eq_refl) as H8. rewrite E8 in H8.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 1) with (pf_sp0 v - 16) in H8 by lia. exact H8.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D16. rewrite G3, Z.add_0_r in D16. rewrite D16.
    replace (16 * (pf_sp0 v / 16)) with (2 * (pf_sp0 v / 16) * 8) by lia. apply Z_mod_mult.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.

Lemma b11z_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1 k low,
  getr regs1 (Z_to_bv 5 9) = w64 s1 -> getr regs1 (Z_to_bv 5 20) = w64 SB ->
  getr regs1 (Z_to_bv 5 13) = w64 k -> 0 <= k <= 23 ->
  4096 <= low -> low + 24 <= 2 ^ 47 ->
  rdword (rdW W memc) (s1 + 0x10) = Some (pf_nt low) ->
  rdword (rdW W memc) (s1 + 0x90) = Some low ->
  apresent (w_H W) memc (low + k) ->
  low + 24 <= s1 -> s1 + 0x98 <= 2 ^ 64 ->
  st_ok_pi SEGS VAL (b11z_E regs1 low k) b11z_ss
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + B11_ZST)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1 k low H9 H20 H13 Hk Hl1 Hl2 Hw10 Hw90 Hp Hs1 Hs2.
set (E := b11z_E regs1 low k).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j [w64 (pf_nt low); w64 low; w64 (low + k)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold b11z_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth] in E32, E33, E34. clear EX.
assert (E9 : ew E 9 = w64 s1) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E13 : ew E 13 = w64 k) by (rewrite (EE 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E20 : ew E 20 = w64 SB) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact H20).
assert (HN : 0 <= pf_nt low < 2 ^ 64) by (unfold pf_nt; lia).
rewrite restrict_mkst_fx. unfold b11z_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ s1 0x10 8 (SOff 32 0) (pf_nt low));
        [cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hw10).
    * apply (chunk_ok_val SEGS E _ s1 0x90 8 (SOff 33 0) low);
        [cbn [sv_denot]; rewrite E33; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hw90).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E34. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact Hp.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E34. unfold w64. rewrite !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E20, E13, E32, E33, E34. unfold w64. rewrite !unsigned_lit_small by (unfold SB, pf_nt; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold pf_nt, SB in *. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I]. apply U_inj.
    rewrite (b11z_u_add E _ _ low k); [| apply U_atom; [exact E33 | lia] | apply U_atom; [exact E13 | lia] | lia].
    symmetry. apply U_atom; [exact E34 | lia].
Qed.

(* ---------- the piece: ZST -> the call -> RBT ---------- *)
Lemma b11z_zst : forall n, B11_RBT_stmt B n -> forall li, B11_ZST_stmt B n li.
Proof.
intros n RBT li v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
destruct HI as (HCX & Hli & Hcap & HLOW & HRG).
pose proof HCX as (HB & HMID & HST & HSTR & HINB & HSL70).
pose proof (b11_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HB) as (GG & Hin & EF & Hfrs & HAR & Hly & HFP & HSP).
pose proof GG as (G1 & G2 & G3 & G4 & G5 & G6 & F1 & F2 & F3 & F4 & _).
pose proof HB as (HCX0 & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & HFRM & HTF & _ & HRG0).
pose proof HTF as (_ & _ & _ & T47 & _). change (fs_frame_bytes 5) with 2048 in T47.
pose proof asan_consts as (AC1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
assert (SBT : STK_reac_box_catalogue_by_token = 8256) by (vm_compute; reflexivity).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof alloc_ceiling_lt as Hac.
unfold b11_low, PF_O_L146 in HLOW. unfold B11_CAP in Hcap.
assert (NFV : nulfree val) by (destruct HSTR as ((_ & NZ) & _); exact NZ).
(* the cut's registers and slots *)
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b11_rg_get rX _ 9 _ HRG0); b11z_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SB) by (rewrite SB_SHADOW_OFF; apply (b11_rg_get rX _ 20 _ HRG0); b11z_in).
assert (R13 : getr rX (Z_to_bv 5 13) = w64 (Z.of_nat li)) by (apply (b11_rg_get rX _ 13 _ HRG); b11z_in).
assert (W10 : rdword (rdW Wc memc) (pf_s1 v + 0x10) = Some (pf_nt (pf_F v pos + 736)))
  by (apply (b11_slot_get _ _ _ _ _ HSL); b11z_in).
assert (W90 : rdword (rdW Wc memc) (pf_s1 v + 0x90) = Some (pf_F v pos + 736))
  by (apply (b11_slot_get _ _ _ _ _ HSL); b11z_in).
(* the seed *)
pose proof (b11z_entry Wc rX memc (pf_s1 v) (Z.of_nat li) (pf_F v pos + 736) R9 R20 R13
  ltac:(lia) ltac:(lia) ltac:(lia) W10 W90 (HFP (pf_F v pos + 736 + Z.of_nat li) ltac:(lia))
  ltac:(lia) ltac:(lia)) as HS.
assert (HEI : img_env VAL A_LIM (b11z_E rX (pf_F v pos + 736) (Z.of_nat li))) by (unfold b11z_E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX [w64 (pf_nt (pf_F v pos + 736)); w64 (pf_F v pos + 736);
    w64 (pf_F v pos + 736 + Z.of_nat li)]) (b11z_E rX (pf_F v pos + 736) (Z.of_nat li)))
  by (split; [intros n0 Hn0; unfold b11z_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E20 : ew (b11z_E rX (pf_F v pos + 736) (Z.of_nat li)) 20 = Z_to_bv 64 SB)
  by (unfold b11z_E; rewrite (ew_Eimg_Ereg_nat rX _ 20 (Z_to_bv 5 20) eq_refl); exact R20).
assert (E33 : ew (b11z_E rX (pf_F v pos + 736) (Z.of_nat li)) 33 = Z_to_bv 64 (pf_F v pos + 736))
  by (unfold b11z_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew (b11z_E rX (pf_F v pos + 736) (Z.of_nat li)) 34 = Z_to_bv 64 (pf_F v pos + 736 + Z.of_nat li))
  by (unfold b11z_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
revert HS HEI HA0 E20 E33 E34. generalize (b11z_E rX (pf_F v pos + 736) (Z.of_nat li)) as E0.
intros E0 HS HEI HA0 E20 E33 E34.
assert (U34 : bv_unsigned (ew E0 34) = pf_F v pos + 736 + Z.of_nat li)
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (UB : U E0 b11z_Bx = SHADOW_OFF)
  by (unfold b11z_Bx; rewrite (U_atom E0 20 SB E20) by (unfold SB; lia); reflexivity).
(* model low's 24 bytes are addressable (its cells 0x5c .. 0x5e are 0 under PF_SC_L146) *)
assert (RAL : range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + 736) 24).
{ apply (b11_ra_frame B v pos lyc Sc Wc rX memc mdc PF_SC_L146 736 24 HB eq_refl eq_refl ltac:(lia) ltac:(lia)
    ltac:(lia)).
  intros i Hi. replace (736 / 8) with 92 in Hi by reflexivity. replace ((736 + 24) / 8) with 95 in Hi by reflexivity.
  apply b11z_shb_l146. exact Hi. }
assert (SHOK : sh_ok SEGS b11z_Bx b11z_SH E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b11z_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b11z_Bx 34%nat (pf_F v pos + 736) 24
    (pf_F v pos + 736 + Z.of_nat li) 0 1 RAL UB ltac:(apply U_atom; [exact E34 | lia])); [lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
  unfold SHADOW_OFF. destruct F4; lia. }
(* the written byte lies in the class-5 frame, which the segment owns *)
assert (HAW : forall a, pf_F v pos + 736 + Z.of_nat li + 0 <= a < pf_F v pos + 736 + Z.of_nat li + 1 ->
  awr_byte SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (ablocks B (p_ly v) (p_S v))
    (ablocks B lyc Sc) (frames (p_S v)) lyc [(5, pos)] a).
{ intros a Ha. right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr.
  cbn [fst snd]. rewrite EF. change (fs_frame_bytes 5) with 2048. lia. }
unfold cfg_at. change (w64 (BASE + B11_ZST)) with (Z_to_bv 64 (BASE + B11_ZST)).
(* 0x889ac .. 0x889d8: T21 (decided), a1 = low, B#26 (covered), low[li] = 0, a0 = low, the call *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b11z_awr1 34%nat U34 HAW. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
lazymatch goal with HS' : st_ok _ ?En _ (restrict _ ?msn) |- _ =>
  assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)); rename msn into ms1 end.
(* ---- at the call 0x889d8: what the run kept, the NUL it wrote, the registers ---- *)
assert (KS : forall a, 0 <= a < 2 ^ 64 -> a <> pf_F v pos + 736 + Z.of_nat li ->
  rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hne.
  apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms1)
    (fun a' => a' = pf_F v pos + 736 + Z.of_nat li) HFr); [|exact Ha | exact Hne].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr;
    [lia | rewrite U34 in Hrr; lia]. }
assert (HW0 : rdW Wc (ms_mem ms1) (pf_F v pos + 736 + Z.of_nat li) = Some 0).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth (segs := SEGS) Ex ssx (restrict (w_H Wc) msx) 1 r1 HS
      ltac:(vm_compute; reflexivity)) as HR1;
    cbn [ms_mem restrict] in HR1;
    pose proof (b11z_cell_of_region Ex (w_H Wc) (ms_mem msx) 34 (pf_F v pos + 736 + Z.of_nat li) _ _ _ _ _ 0 0 HR1)
      as V end.
  rewrite Z.add_0_r in V. apply V.
  - rewrite (b11z_ag_ew E0 _ 40 34 _ HAE ltac:(lia) E34). apply unsigned_lit_small. lia.
  - vm_compute. reflexivity. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
  assert (HA1 : env_agree 32 (Ereg rX [w64 (pf_nt (pf_F v pos + 736)); w64 (pf_F v pos + 736);
      w64 (pf_F v pos + 736 + Z.of_nat li)]) Ex) by exact (b11z_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE) end.
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX _ HS HA1 ltac:(vm_compute; reflexivity)) as HPR1.
b11z_reg HS (10%bv : bv 5) Q10.
b11z_reg HS (1%bv : bv 5) Q1.
assert (R10 : getr (ms_regs ms1) 10 = w64 (pf_F v pos + 736)).
{ pose proof (b11z_reg_atom _ _ _ 33 0 (pf_F v pos + 736) Q10 (b11z_ag_ew E0 _ 40 33 _ HAE ltac:(lia) E33)
    ltac:(lia)) as R.
  rewrite Z.add_0_r in R. exact R. }
assert (C1 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + 15388)).
{ rewrite Q1. lazymatch goal with H : img_env _ _ ?En |- context [sv_denot ?En _] =>
    exact (codeptr_val En 15388 H) end. }
pmkst HS.
assert (KR : forall r z, In r [2; 3; 4; 8; 9; 20] -> getr rX (Z_to_bv 5 r) = w64 z ->
  getr (ms_regs ms1) (Z_to_bv 5 r) = w64 z).
{ intros r z Hr Hz. rewrite (HPR1 r) by (cbn [In] in Hr; unfold acallee_saved; lia). exact Hz. }
assert (C2 : getr (ms_regs ms1) 2 = w64 (pf_s1 v))
  by (apply (KR 2); [b11z_in | apply (b11_rg_get rX _ 2 _ HRG0); b11z_in]).
assert (C3 : getr (ms_regs ms1) 3 = w64 (as_gp B))
  by (apply (KR 3); [b11z_in | apply (b11_rg_get rX _ 3 _ HRG0); b11z_in]).
assert (C4 : getr (ms_regs ms1) 4 = w64 (as_tp B))
  by (apply (KR 4); [b11z_in | apply (b11_rg_get rX _ 4 _ HRG0); b11z_in]).
assert (C8 : getr (ms_regs ms1) 8 = w64 (pf_sp0 v))
  by (apply (KR 8); [b11z_in | apply (b11_rg_get rX _ 8 _ HRG0); b11z_in]).
assert (Csp : spZ (ms_regs ms1) = pf_s1 v)
  by (unfold spZ; rewrite C2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
(* b11_cx at the call state: the run wrote only low + li, a byte of model low *)
assert (KP1 : b11_kept v pos false None (rdW Wc memc) (rdW Wc (ms_mem ms1))).
{ split.
  - intros a Ha Hn. apply KS; [exact Ha|]. intros ->. apply Hn. unfold b11_Wr, PF_O_L146. right; left. lia.
  - intros a _ Hv. exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms1) a HG Hv). }
assert (HFI1 : pf_rg (ms_regs ms1) (b11_FI B v))
  by exact (b11_rg_pres rX (ms_regs ms1) _ HPR1 (b11_FI_cs B v) HRG0).
pose proof (b11_cx_move B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Sc Wc (ms_regs ms1) (ms_mem ms1) mdv
  HCX HJ (ex_intro _ (st_fs Sc) (eq_sym (b11z_set_fs_id Sc))) (Permutation_refl _) KP1 HFI1) as HCX1.
pose proof HCX1 as (HB1 & _).
pose proof HB1 as (_ & _ & HOBJ1 & _ & HFSH1).
pose proof HOBJ1 as (_ & _ & _ & _ & _ & CAT1 & _ & ROD1 & _).
destruct (b11z_chain v pos lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv PF_SC_L146 HB1) as [ch1 HCH].
(* model low holds the folded value and its NUL *)
assert (STR1 : sa_str (rdW Wc (ms_mem ms1)) (pf_F v pos + 736) (r_low val 0 24)).
{ split; [split|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite <- Hli in Hi.
    destruct (Nat.lt_ge_cases i li) as [Hil | Hil].
    + rewrite app_nth1 by lia. rewrite KS by lia. rewrite (HLOW i Hil). f_equal. symmetry.
      apply b11z_nth_low; [exact NFV | lia].
    + assert (i = li) by lia. subst i. rewrite app_nth2 by lia. rewrite <- Hli, Nat.sub_diag. exact HW0.
  - apply b11f_low_nulfree. exact NFV.
  - intros x Hx. rewrite <- Hli in Hx.
    pose proof (Z.mod_pos_bound (pf_F v pos + 736 + Z.of_nat li) 8 ltac:(lia)).
    apply (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms1) x HG). apply (aview_some_of_apresent SEGS).
    apply HFP. lia. }
assert (ADDR1 : sa_addr (rdW Wc (ms_mem ms1)) (pf_F v pos + 736) (Z.of_nat (length (r_low val 0 24)) + 1))
  by (apply (b11z_addr_low v pos _ _ _ GG HFSH1); lia).
assert (BTP : by_token_pre SEGS B lyc Sc (rdW Wc (ms_mem ms1)) catA (pf_F v pos + 736) (r_low val 0 24)).
{ split; [lia|]. split; [exact STR1|]. split; [exact ADDR1|].
  split.
  { right; left. exists 5, pos. split; [exact Hin|]. split; [lia|]. rewrite EF. change (fs_frame_bytes 5) with 2048.
    lia. }
  split; [lia | exact CAT1]. }
assert (EVB : st_nev Sc + EV_reac_box_catalogue_by_token <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
  pose proof HCX0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev).
  unfold EV_reac_box_catalogue_by_token, EV_reac_segconf_parse_file in *. lia. }
(* ---- 0x889d8 jal reac_box_catalogue_by_token: the call target is the program's function ---- *)
rewrite (SIGP SS_reac_box_catalogue_by_token
  ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_box_catalogue_by_token) with AF_reac_box_catalogue_by_token by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS (fx := fx) B LAWS Wc (ms_regs ms1) (ms_mem ms1) _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0
    STK_reac_box_catalogue_by_token [] EV_reac_box_catalogue_by_token (pf_s1 v - pf_sp0 v)
    (Z_to_bv 64 (BASE + 15388)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (seg_spec.cat_ptr catA (by_token (r_low val 0 24))) /\
       sa_kept SEGS Wc (ms_mem ms1) W2 mem2 (ms_regs ms1) STK_reac_box_catalogue_by_token (fun _ => False) /\
       sa_noalloc B lyc Sc ly2 S2) HJ).
  - rewrite Csp. lia.
  - apply b11_m16; [exact G6 | exact G3].
  - lia.
  - rewrite SBT. lia.
  - rewrite SBT, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (BYTOKEN fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv ch1 (pf_F v pos + 736) (r_low val 0 24) HPRE1 ROD1
        R10 ltac:(lia) BTP EVB). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a (r & Hr & _). destruct Hr. }
(* ---- back at 0x889dc (RBT) ---- *)
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (HA10 & HKEPT & HNA)).
destruct HNA as (HPm2 & Hly2 & HSf2). subst ly2.
unfold sa_kept in HKEPT.
change (0 + EV_reac_box_catalogue_by_token) with 0 in HJ2.
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
(* the callee wrote only its window [s1 - 8256, s1), whose bytes stay present *)
assert (KP2 : b11_kept v pos false None (rdW Wc (ms_mem ms1)) (rdW W2 mem2)).
{ split.
  - intros a Ha Hn. apply HKEPT; [exact Ha | | intros Hf; exact Hf].
    rewrite Csp, SBT. intros Hw. apply Hn. unfold b11_Wr. left. rewrite SPF. lia.
  - intros a Ha Hv.
    destruct (Z_lt_le_dec a (pf_s1 v - 8256)) as [Hlo | Hlo];
      [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
    + rewrite HKEPT; [exact Hv | exact Ha | rewrite Csp, SBT; lia | intros Hf; exact Hf].
    + pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
      apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite SBT. lia.
    + rewrite HKEPT; [exact Hv | exact Ha | rewrite Csp, SBT; lia | intros Hf; exact Hf]. }
assert (HFI2 : pf_rg regs2 (b11_FI B v)) by exact (b11_rg_pres (ms_regs ms1) regs2 _ HP2 (b11_FI_cs B v) HFI1).
pose proof (b11_cx_move B n v pos lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv cf nm o ln d gi vp val S2 W2 regs2 mem2
  md2 HCX1 HJ2 HSf2 HPm2 KP2 HFI2) as HCX2.
(* model low's string is outside the callee's window *)
assert (STR2 : sa_str (rdW W2 mem2) (pf_F v pos + 736) (r_low val 0 24)).
{ apply (b11z_str_keep _ _ _ _ STR1). intros x Hx. rewrite <- Hli in Hx.
  apply HKEPT; [lia | rewrite Csp, SBT; lia | intros Hf; exact Hf]. }
(* the registers: PF_RL / PF_RM callee-saved through the run and the call, a0 = by_token's answer *)
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR1 HP2).
assert (RG2 : pf_rg regs2 (PF_RL v pos ++ PF_RM v o ln ++
    [(10, seg_spec.cat_ptr catA (by_token (r_low val 0 24)))])).
{ pose proof (proj1 (b11_rg_app rX _ _) HRG) as (RL & RMX).
  pose proof (proj1 (b11_rg_app rX _ _) RMX) as (RM & _).
  apply (proj2 (b11_rg_app regs2 _ _)). split; [exact (b11_rg_pres rX regs2 _ HPR2 (b11_RL_cs v pos) RL)|].
  apply (proj2 (b11_rg_app regs2 _ _)). split; [exact (b11_rg_pres rX regs2 _ HPR2 (b11_RM_cs v o ln) RM)|].
  unfold pf_rg. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact HA10. }
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 15388)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + B11_RBT) regs2 mem2 md2).
apply (RBT v pos lyc S2 W2 regs2 mem2 md2 cf nm o ln d gi vp val).
split; [exact HCX2|]. split; [exact STR2 | exact RG2].
Qed.
End x.

(* the piece at every FP state *)
Theorem b11_zst_ok : forall (fx : YK11.FPState) (n : nat),
  B11_RBT_stmt (fx := fx) B n -> forall li, B11_ZST_stmt (fx := fx) B n li.
Proof. intros fx n H li. exact (b11z_zst (fx := fx) n H li). Qed.
End d.
