(* The shared vocabulary of the walk of reac_segconf_declared (fuzz_segconf.asan, image A, entry 0x89854 =
   BASE + AF_reac_segconf_declared, 206 instructions) in plugin-hostd/fuzz_command's lib/A/Prog form: the context
   record, the cut points, the contract's premises and post over the context, the frame part and the kept part of
   every cut, the cut invariants and the "from a cut point" predicates (the form of fuzz_command's
   chain_words_d.v, with check_reply's class-1 side-stack frame, check_reply_k.v / check_reply_s8.v).
   The cut points (offsets from the function's entry):
     KL 0x16c (0x899c0)  the head of the loop over c->seg, pass i (the inline check of seg[i].ignore is next)
     KA 0x1ac (0x89a00)  reac_declared_vlan_split returned 1; the load of vid and the add call are next
     KT 0x1e0 (0x89a34)  the latch: pass i done; the inline check of c->n is next
     KX 0x224 (0x89a78)  the join before the release of the frame; 56(s1) holds the result
   The segments (one file each, reac_segconf_declared_s1.v .. _s5.v): S1 entry -> KL 0 | KX 0; S2 KL i -> KT i |
   KA i; S3 KA i -> KT i | KX (-1); S4 KT i -> KL (i + 1) | KX added; S5 KX r -> the return.
   The program calls compose through cl_callS_wide (PaNoChain.v): split writes parent [F + 32, F + 48) and vid
   [F + 64, F + 66) in this walk's own class-1 frame, add writes the table's next entry and *n, both in the
   footprint of this walk's journal. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* the cut points, as offsets from the listing's start (BASE + DC_K* is the address) *)
Definition DC_KL : Z := AF_reac_segconf_declared + 0x16c.
Definition DC_KA : Z := AF_reac_segconf_declared + 0x1ac.
Definition DC_KT : Z := AF_reac_segconf_declared + 0x1e0.
Definition DC_KX : Z := AF_reac_segconf_declared + 0x224.
(* the registers the prologue saves, in the order of their slots: slot j at sp0 - 8 - 8 j (ra at 184(sp), s0 at
   176(sp), ..., s11 at 88(sp), with sp = sp0 - 192) *)
Definition dc_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
(* the struct reac_segconf fields the code reads: c->n (RC_N) and seg[i].ignore (RS_IGNORE) *)
Definition DC_RC_N : Z := 0x2c80.
Definition DC_IGN : Z := 24.
(* the realigned stack pointer of 0x89894 (`andi sp,sp,-32` after `addi sp,sp,-192`) *)
Definition dc_sp1 (sp0 : Z) : Z := (sp0 - 192) - (sp0 - 192) mod 32.
Lemma dc_sp1_facts : forall sp0, sp0 mod 16 = 0 ->
  dc_sp1 sp0 mod 32 = 0 /\ (dc_sp1 sp0 = sp0 - 192 \/ dc_sp1 sp0 = sp0 - 208).
Proof.
intros sp0 H. unfold dc_sp1. pose proof (Z.mod_pos_bound (sp0 - 192) 32 ltac:(lia)) as M.
assert (Hm : (sp0 - 192) mod 32 = 0 \/ (sp0 - 192) mod 32 = 16).
{ pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)) as D. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
  rewrite H in D2. lia. }
split; [|lia].
replace ((sp0 - 192) - (sp0 - 192) mod 32) with (32 * ((sp0 - 192) / 32))
  by (pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the values the walk keeps from the entry: the statement's binders, and the position of the class-1 side-stack
   frame that __asan_stack_malloc_1 hands back (x_fpos; any value before that call) *)
Record dcx : Type := mkDCX {
  x_ly : alayout; x_S : astate; x_W : world SEGS; x_regs : bvmap 5 word; x_mem : word -> option byte; x_md : Model;
  x_ch : list (Z * Z * Z); x_c : Z; x_tab : Z; x_max : Z; x_n : Z;
  x_rc : rconf; x_tb : list (list Z * Z); x_fpos : Z }.
Definition dc_setpos (c : dcx) (f : Z) : dcx :=
  mkDCX (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c) (x_c c) (x_tab c)
    (x_max c) (x_n c) (x_rc c) (x_tb c) f.
(* the entry stack pointer, the realigned one, the frame, its flag cell, its shadow; the loop's bound *)
Definition dc_sp0 (c : dcx) : Z := spZ (x_regs c).
Definition dc_s1 (c : dcx) : Z := dc_sp1 (dc_sp0 c).
Definition dc_F (c : dcx) : Z := frame_addr (x_ly c) 1 (x_fpos c).
Definition dc_FL (c : dcx) : Z := flag_addr (x_ly c) 1 (x_fpos c).
Definition dc_segs (c : dcx) : list rseg := rc_seg (x_rc c).
Definition dc_nn (c : dcx) : Z := Z.of_nat (length (dc_segs c)).
(* the three argument words the prologue stores at 32/40/48(s1) *)
Definition dc_a1 (c : dcx) : Z := bv_unsigned (getr (x_regs c) 11).
Definition dc_a2 (c : dcx) : Z := bv_unsigned (getr (x_regs c) 12).
Definition dc_a3 (c : dcx) : Z := bv_unsigned (getr (x_regs c) 13).
Section e.
Variable B : asyms.
(* the contract's image parameters: the stack window, the read-only window, the stack-protector GOT word and guard *)
Variables STK RLO RHI GOTW GUARD : Z.
(* the final result and table of the model *)
Definition dc_res (c : dcx) : Z * list (list Z * Z) := r_declared (x_rc c) (x_tb c) (x_max c).
(* reac_segconf_declared_contract's premises (reac_segconf_declared_c.v:133-140) over the context *)
Record dc_pre (c : dcx) : Prop := mkDCPre {
  cp_afn : afn_pre SEGS B STK (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c);
  cp_rod : arodata_okP SEGS RLO RHI B (rdW (x_W c) (x_mem c));
  cp_a0 : getr (x_regs c) 10 = w64 (x_c c);
  cp_c64 : 0 <= x_c c < 2 ^ 64;
  cp_a1 : getr (x_regs c) 11 = w64 (x_tab c);
  cp_tab64 : 0 <= x_tab c < 2 ^ 64;
  cp_a2 : getr (x_regs c) 12 = w64 (x_max c);
  cp_max64 : 0 <= x_max c < 2 ^ 64;
  cp_a3 : getr (x_regs c) 13 = w64 (x_n c);
  cp_n64 : 0 <= x_n c < 2 ^ 64;
  cp_dpre : declared_pre SEGS B (x_ly c) (x_S c) (x_W c) (x_mem c) (x_regs c) (x_c c) (x_tab c) (x_max c) (x_n c)
    (x_rc c) (x_tb c) GOTW GUARD;
  cp_room : sa_room (x_S c);
  cp_nev : st_nev (x_S c) + EV_reac_segconf_declared <= EV_MAX }.
(* the footprint and the post, as the contract states them (reac_segconf_declared_c.v:142-149) *)
Definition dc_FP (c : dcx) : list (Z * Z) := declared_W (x_tab c) (x_n c) (x_tb c) (snd (dc_res c)).
Definition dc_Q (c : dcx) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (fst (SegModel.r_declared (x_rc c) (x_tb c) (x_max c))) /\
 sa_rtab (aview SEGS (w_H W') mem') (x_tab c) (snd (SegModel.r_declared (x_rc c) (x_tb c) (x_max c))) /\
 sa_val (aview SEGS (w_H W') mem') (x_n c) 4 (Z.of_nat (length (snd (SegModel.r_declared (x_rc c) (x_tb c) (x_max c))))) /\
 (sa_guardtab (aview SEGS (w_H (x_W c)) (x_mem c)) (x_tab c) (x_max c) ->
  sa_guardtab (aview SEGS (w_H W') mem') (x_tab c) (x_max c)) /\
 sa_noalloc B (x_ly c) (x_S c) ly' S'.
Definition dc_post (c : dcx) : world SEGS -> config -> Prop :=
  apost_base SEGS B STK (dc_FP c) (x_regs c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    EV_reac_segconf_declared (dc_Q c).
(* the table ti at tab and the count cell n = |ti| at a state: what add asks of them and gives back; the table
   only grows, and never past max *)
Definition dc_tab (c : dcx) (ti : list (list Z * Z)) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  sa_rtab (rdW W3 mem3) (x_tab c) ti /\ sa_val (rdW W3 mem3) (x_n c) 4 (Z.of_nat (length ti)) /\
  (length (x_tb c) <= length ti)%nat /\ Z.of_nat (length ti) <= x_max c.
(* the frame part of every cut: the walk's journal from the entry with the class-1 frame as its own frame, the
   registers the code keeps (sp = s1 = the realigned sp, s0 = sp0, s3 = the frame's shadow, s4 = the shadow base),
   the saved registers in their slots, the frame at 16(s1) and 24(s1) (the release reads both), the arguments
   tab / max / n at 32/40/48(s1) (the add call reloads them), and the frame's flag pointer at frame + 120 *)
Record dc_fi (c : dcx) (k : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop := mkDCFi {
  fi_j : ajournal SEGS B STK (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(1, x_fpos c)] ly3 S3 W3 mem3 md3 k;
  fi_sp : getr regs3 2 = w64 (dc_s1 c);
  fi_gp : getr regs3 3 = w64 (as_gp B);
  fi_tp : getr regs3 4 = w64 (as_tp B);
  fi_s0 : getr regs3 8 = w64 (dc_sp0 c);
  fi_s1 : getr regs3 9 = w64 (dc_s1 c);
  fi_s3 : getr regs3 19 = w64 (SB + dc_F c / 8);
  fi_s4 : getr regs3 20 = w64 SB;
  fi_saved : forall j r, nth_error dc_saved j = Some r ->
    rdword (rdW W3 mem3) (dc_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)));
  fi_f16 : rdword (rdW W3 mem3) (dc_s1 c + 16) = Some (dc_F c);
  fi_f24 : rdword (rdW W3 mem3) (dc_s1 c + 24) = Some (dc_F c);
  fi_tab : rdword (rdW W3 mem3) (dc_s1 c + 32) = Some (dc_a1 c);
  fi_max : rdword (rdW W3 mem3) (dc_s1 c + 40) = Some (dc_a2 c);
  fi_n : rdword (rdW W3 mem3) (dc_s1 c + 48) = Some (dc_a3 c);
  fi_flag : rdword (rdW W3 mem3) (dc_F c + 120) = Some (dc_FL c) }.
(* the part of every cut the journal of dc_fi does not give: the blocks are a permutation of the entry's, the
   layout is the entry's, and the state is the entry's up to its side-stack part (every callee's sa_noalloc). The
   bytes the calls keep (the image outside the runtime's statics and errno, a block's bytes outside the footprint,
   an entry frame's bytes and shadow outside the footprint, the bytes above the allocator's ceiling outside the
   stack window and the footprint) are the journal's own clauses (YCbq.v ajournal). *)
Record dc_un (c : dcx) (ly3 : alayout) (S3 : astate) : Prop := mkDCUn {
  un_perm : Permutation (ablocks B ly3 S3) (ablocks B (x_ly c) (x_S c));
  un_ly : ly3 = x_ly c;
  un_fs : exists f, S3 = set_fs f (x_S c) }.
(* the loop's state: the table ti in memory, the count added so far, and the model's remaining run *)
Definition dc_loop (c : dcx) (i : nat) (ti : list (list Z * Z)) (added : Z) : Prop :=
  r_decl_go (skipn i (dc_segs c)) ti (x_max c) added = r_declared (x_rc c) (x_tb c) (x_max c) /\
  0 <= added <= Z.of_nat i.
(* the registers of the loop at KL / KT, pass i: s7 = i, s6 = &seg[i], s9 = &seg[i].ignore, s8 = &c->n,
   s5 = the shadow byte of s8 written as (s8 >> 3) + SB, s10 = parent, s11 = vid, s2 = 0xf8 sign-extended *)
Definition dc_lregs (c : dcx) (i : Z) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 23 = w64 i /\ getr regs3 22 = w64 (x_c c + 356 * i) /\
  getr regs3 25 = w64 (x_c c + 356 * i + DC_IGN) /\ getr regs3 24 = w64 (x_c c + DC_RC_N) /\
  getr regs3 21 = w64 (SB + (x_c c + DC_RC_N) / 8) /\
  getr regs3 26 = w64 (dc_F c + 32) /\ getr regs3 27 = w64 (dc_F c + 64) /\ getr regs3 18 = w64 (-8).
(* the cut invariants. KL / KT carry the frame part at the journal's count 0 and the kept part; 56(s1) holds the
   count added so far (a sign-extended word) *)
Definition INV_KL (c : dcx) (i : nat) (ti : list (list Z * Z)) (added : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dc_fi c 0 ly3 S3 W3 regs3 mem3 md3 /\ dc_un c ly3 S3 /\ dc_tab c ti W3 mem3 /\
  (i < length (dc_segs c))%nat /\ dc_loop c i ti added /\ dc_lregs c (Z.of_nat i) regs3 /\
  rdword (rdW W3 mem3) (dc_s1 c + 56) = Some added.
Definition INV_KT (c : dcx) (i : nat) (ti : list (list Z * Z)) (added : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dc_fi c 0 ly3 S3 W3 regs3 mem3 md3 /\ dc_un c ly3 S3 /\ dc_tab c ti W3 mem3 /\
  (i < length (dc_segs c))%nat /\ dc_loop c (S i) ti added /\ dc_lregs c (Z.of_nat i) regs3 /\
  rdword (rdW W3 mem3) (dc_s1 c + 56) = Some added.
(* KA: pass i, split gave (p, v): parent holds p with its NUL, vid holds v; the frame's shadow says parent's 16
   bytes and vid's 2 bytes are addressable (bytes 4, 5 = 0, byte 8 = 2) *)
Definition INV_KA (c : dcx) (i : nat) (ti : list (list Z * Z)) (added : Z) (p : list Z) (v : Z)
  ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dc_fi c 0 ly3 S3 W3 regs3 mem3 md3 /\ dc_un c ly3 S3 /\ dc_tab c ti W3 mem3 /\
  (i < length (dc_segs c))%nat /\ dc_loop c i ti added /\ dc_lregs c (Z.of_nat i) regs3 /\
  rdword (rdW W3 mem3) (dc_s1 c + 56) = Some added /\
  rs_ignore (nth i (dc_segs c) rseg_d) = false /\ vlan_split (rs_name (nth i (dc_segs c) rseg_d)) = Some (p, v) /\
  sa_strz (rdW W3 mem3) (dc_F c + 32) p /\ sa_val (rdW W3 mem3) (dc_F c + 64) 2 v /\
  rdW W3 mem3 (SB + dc_F c / 8 + 4) = Some 0 /\ rdW W3 mem3 (SB + dc_F c / 8 + 5) = Some 0 /\
  rdW W3 mem3 (SB + dc_F c / 8 + 8) = Some 2.
(* KX: the result and the final table, in 56(s1) (the result as a 64-bit word) and in memory *)
Definition INV_KX (c : dcx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  dc_fi c 0 ly3 S3 W3 regs3 mem3 md3 /\ dc_un c ly3 S3 /\ dc_tab c (snd (dc_res c)) W3 mem3 /\
  rdword (rdW W3 mem3) (dc_s1 c + 56) = Some (fst (dc_res c) mod 2 ^ 64).
(* "from this cut point the walk reaches the post" *)
Definition dc_from (pc : Z) (INV : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (c : dcx) : Prop :=
  forall ly3 S3 W3 regs3 mem3 md3, INV ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + pc) regs3 mem3 md3) (dc_post c).
Definition from_KL (c : dcx) (i : nat) : Prop :=
  forall ti added, dc_from DC_KL (INV_KL c i ti added) c.
Definition from_KT (c : dcx) (i : nat) : Prop :=
  forall ti added, dc_from DC_KT (INV_KT c i ti added) c.
Definition from_KA (c : dcx) (i : nat) : Prop :=
  forall ti added p v, dc_from DC_KA (INV_KA c i ti added p v) c.
Definition from_KX (c : dcx) : Prop := dc_from DC_KX (INV_KX c) c.
Lemma dc_pre_setpos : forall c f, dc_pre c -> dc_pre (dc_setpos c f).
Proof. intros c f H. destruct H. constructor; assumption. Qed.
Lemma dc_post_setpos : forall c f, dc_post (dc_setpos c f) = dc_post c.
Proof. reflexivity. Qed.
(* the two image facts the segments take until the record's image files land (discharged at the top): the
   read-only window lies in the image, and the stack-protector GOT word and guard split's strtol compares are
   readable as sa_ssp asks at every state the allocator invariant holds in *)
Definition dc_ro_imgP : Prop := forall a, RLO <= a < RHI -> in_img SEGS a.
Definition dc_sspP : Prop := forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) GOTW GUARD.
End e.
End f.
End d.
(* the segments of the walk (one file each); reac_segconf_declared_a.v chains them *)
Section sp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Variable B : asyms.
Variables STK RLO RHI GOTW GUARD : Z.
#[local] Notation PRE := (dc_pre B STK RLO RHI GOTW GUARD).
Definition dc_S1P : Prop := forall c, PRE c ->
  (forall f, from_KX B STK (dc_setpos c f)) -> (forall f, from_KL B STK (dc_setpos c f) 0) ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_reac_segconf_declared) (x_regs c) (x_mem c) (x_md c)) (dc_post B STK c).
Definition dc_S2P : Prop := forall c i, PRE c ->
  from_KT B STK c i -> from_KA B STK c i -> from_KL B STK c i.
Definition dc_S3P : Prop := forall c i, PRE c ->
  from_KT B STK c i -> from_KX B STK c -> from_KA B STK c i.
Definition dc_S4P : Prop := forall c i, PRE c ->
  from_KL B STK c (S i) -> from_KX B STK c -> from_KT B STK c i.
Definition dc_S5P : Prop := forall c, PRE c -> from_KX B STK c.
End sp.
