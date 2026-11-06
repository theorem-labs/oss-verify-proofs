(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/ParseModel.v at 3e9fc5c8969 (lines
   57-58 walk_pairs, 76-80 vcell, 83-89 fold_after, 91-108 ha_fold_cons / parse_cell_vcell / walk_pairs_step) with
   module paths changed and the names prefixed hp_; the call record, the cut core and the model facts per cut are in
   the form of proofs/reac-pw/fuzz_role/lib/A/RPgParseBase.v at afaa3cb55c1 (pctx, call_ok, PPOST, SAVED, FI),
   restated for headamp's contract (lib/A/HPgCSpec.v hd_parse_result_specX) and for the frame hole of lib/A/HPgHole.v
   (the core carries hjournal in place of ajournal). *)
(* reac-pw/fuzz_headamp: the IMAGE-INDEPENDENT part of the cut states of reac_headamp_prop_parse_result's walks in
   image A (fuzz_headamp.asan, lib/A/HPgParseCut.v) and image B (fuzz_headamp.asan-ubsan, lib/AU/HPgParseCut.v).
   Statement text only; no function is proved here. Proves no function (kind: statement text).

   What both images do the same way (measured on the pinned images, capstone over the unstripped twins b5f352154c54
   and 1674e30a0698): the prologue `addi sp,sp,-0x100`, the thirteen saves ra, s0 .. s11 at sp0 - 8 .. sp0 - 104 and
   fs0 at sp0 - 112 (sp0 the entry sp), s0 = sp0, `andi sp,sp,-0x20` (spa below), s1 = res, s2 = cap, s3 = out,
   s11 = the shadow offset (read through the .got word), s10 = the shadow address of the frame object
   hd_fr spa = spa + 0x40 (lib/A/HPgHole.v), the hole's eight shadow bytes opened after the entry and closed before
   the one `ret`, and the epilogue `addi sp,s0,-0x100` with the reloads.

   The record hp_ctx is one call: the caller's journal and state at the call (hd_pre's quantities), the call's
   registers, the contract's null flag, pod P with its bytes bs, out O, res R, cap, errno value ev, and the read-only
   window RLO .. RHI. hp_call_ok is hd_parse_result_specX's premise list on it; hp_post its post. hp_core is what
   every cut between the hole's opening and its closing carries: the caller's journal over the unpoisoned memory
   (HPgHole.hjournal at hd_fr spa with the pattern pat), the I/O state, every byte outside the parse's stack window,
   outside the hole's eight shadow bytes and outside the parse's writes as at the call, the saved words, the cells
   written to out, res's twelve bytes, the errno cell readable, and the registers both images keep. The hp_m_* are
   the model facts each cut states of the Pod model (Pod/Headamp.v parse_model, read through Pod/Spa.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================= the model, one pair at a time ======================================= *)
(* The pairs from the child at offset cc of the params Struct at r on, with n passes of fuel and the key slot km
   (Pod/Headamp.v parse_model on VPods: pairs_by spa_get_string over the Struct's children). *)
Definition hp_walk_pairs (bs : list byte) (r cc : Z) (n : nat) (km : option (list byte))
  : list (list byte * Model.ent) :=
Accessors.pairs_by Spa.spa_get_string
  (map (Spa.child_at bs) (Spa.struct_children bs (r + 16) (Spa.u32_at bs (r + 8)) cc n)) km.

(* value_pod_to_byte and value_in_range of a key whose verdict is the cell address (ch, p): parse_cell's KCell arm. *)
Definition hp_vcell (ch p : Z) (v : Model.ent) : Z + Headamp.cell :=
match Headamp.parse_value v with
| Some b => if Headamp.value_in_range p b then inr (ch, p, b) else inl Headamp.REFUSE_OUT_OF_RANGE
| None => inl Headamp.REFUSE_OUT_OF_RANGE
end.

(* ha_fold's step on a pair whose key has the prefix, from the pair's verdict v on. *)
Definition hp_fold_after (cap : Z) (v : Z + Headamp.cell) (rest : list (list byte * Model.ent))
  (cl : list Headamp.cell) (keys rf : Z) : list Headamp.cell * Z * Z :=
match v with
| inl bad => Headamp.ha_fold Headamp.parse_cell cap rest cl (keys + 1)
               (if rf =? Headamp.REFUSE_NONE then bad else rf)
| inr cv => if cap <=? Z.of_nat (length cl) then (cl, keys + 1, rf)
            else Headamp.ha_fold Headamp.parse_cell cap rest (cl ++ [cv]) (keys + 1) rf
end.

Lemma hp_ha_fold_cons : forall cap k v rest cl keys rf,
Headamp.ha_fold Headamp.parse_cell cap ((k, v) :: rest) cl keys rf =
if Headamp.ha_prefix k then hp_fold_after cap (Headamp.parse_cell k v) rest cl keys rf
else Headamp.ha_fold Headamp.parse_cell cap rest cl keys rf.
Proof. intros. cbn [Headamp.ha_fold]. destruct (Headamp.ha_prefix k); reflexivity. Qed.

Lemma hp_parse_cell_vcell : forall k v ch p,
Headamp.parse_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p ->
Headamp.parse_cell k v = hp_vcell ch p v.
Proof. intros k v ch p H. unfold Headamp.parse_cell. rewrite H. reflexivity. Qed.

Lemma hp_walk_pairs_step : forall bs r cc n km,
hp_walk_pairs bs r cc (S n) km =
if Spa.pod_is_inside bs (r + 16) (Spa.u32_at bs (r + 8)) cc then
  match km with
  | None => hp_walk_pairs bs r (cc + Spa.round_up8 (8 + Spa.u32_at bs cc)) n (Spa.spa_get_string (Spa.child_at bs cc))
  | Some k => (k, Spa.child_at bs cc) :: hp_walk_pairs bs r (cc + Spa.round_up8 (8 + Spa.u32_at bs cc)) n None
  end
else [].
Proof. intros. unfold hp_walk_pairs. cbn [Spa.struct_children]. destruct (Spa.pod_is_inside _ _ _ _); reflexivity. Qed.

(* ======================================= the saved words ======================================= *)
(* (offset from the entry sp, register) of the thirteen saves `sd ra,0xf8(sp)` .. `sd s11,0x98(sp)` after
   `addi sp,sp,-0x100`; fs0 at sp0 + HP_FS0 (`fsd fs0,0x90(sp)`). *)
Definition HP_SAVED : list (Z * Z) :=
[(-8, 1); (-16, 8); (-24, 9); (-32, 18); (-40, 19); (-48, 20); (-56, 21); (-64, 22); (-72, 23); (-80, 24);
 (-88, 25); (-96, 26); (-104, 27)].
Definition HP_FS0 : Z := -112.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {segs : list Segment}.
Variable B : asyms.
Variable MT : ameter_ops.

(* ======================================= one call ======================================= *)
Record hp_ctx := HPCtx {
hx_STK : Z; hx_sp0 : Z; hx_FP : list (Z * Z); hx_ly : alayout; hx_S : astate; hx_W0 : world segs;
hx_mem0 : word -> option byte; hx_md0 : Model; hx_own : list (Z * Z);
hx_lyc : alayout; hx_Sc : astate; hx_W : world segs; hx_memc : word -> option byte; hx_mdc : Model; hx_k : Z;
hx_regs : bvmap 5 word;
hx_null : Z; hx_P : Z; hx_O : Z; hx_R : Z; hx_cap : Z; hx_ev : Z; hx_bs : list byte;
hx_RLO : Z; hx_RHI : Z }.

(* the entry sp, the sp after `andi sp,sp,-0x20` (spa), the frame object and its first shadow byte *)
Definition hx_sp (x : hp_ctx) : Z := spZ (hx_regs x).
Definition hx_spa (x : hp_ctx) : Z := Z.land (hx_sp x - 0x100) (-32).
Definition hx_fr (x : hp_ctx) : Z := hd_fr (hx_spa x).
Definition hx_shf (x : hp_ctx) : Z := shadow_addr (hx_fr x).
Definition hx_len (x : hp_ctx) : Z := Z.of_nat (length (hx_bs x)).
Definition hx_SZ (x : hp_ctx) : Z := Spa.u32_at (hx_bs x) 0.
(* the answer of the call, and of a non-NULL call *)
Definition hx_ans (x : hp_ctx) : answer := Headamp.parse_props (hd_props (hx_null x) (hx_bs x)) (hx_cap x).
Definition hx_res (x : hp_ctx) : answer := Headamp.parse_model (hx_bs x) (hx_cap x).
Definition hx_rd (x : hp_ctx) (mem : word -> option byte) : word -> option byte := mrestrict (w_H (hx_W x)) mem.
Definition hx_view (x : hp_ctx) (mem : word -> option byte) : reader := aview segs (w_H (hx_W x)) mem.

(* the contract's post for the call *)
Definition hp_post (x : hp_ctx) : world segs -> config -> Prop :=
hd_parse_post segs B MT (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x)
  (hx_own x) (hx_k x) (hx_regs x) (hx_lyc x) (hx_Sc x) (hx_W x) (hx_memc x) (hx_mdc x) (hx_O x) (hx_R x) (hx_ans x).

Section l.
(* the image's literals: "reac.headamp.", "phantom", "pad", "sens", the stack-guard cells and the doubles *)
Variables akey aph apad asens gotw guard : Z.
Variable dcs : list (Z * Z).
(* hd_parse_result_specX's premises on the call *)
Definition hp_call_ok (x : hp_ctx) : Prop :=
hd_pre segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_k x) T_parse_STK (hx_regs x) (hx_lyc x) (hx_Sc x) (hx_W x) (hx_memc x) (hx_mdc x) /\
0 <= hx_null x <= 1 /\
getr (hx_regs x) 10 = w64 (if hx_null x =? 0 then hx_P x else 0) /\ getr (hx_regs x) 11 = w64 (hx_O x) /\
getr (hx_regs x) 12 = w64 (hx_cap x) /\ getr (hx_regs x) 13 = w64 (hx_R x) /\
hd_parse_args segs B (hx_STK x) (hx_sp0 x) (hx_ly x) (hx_S x) (hx_lyc x) (hx_Sc x) (hx_W x) (hx_memc x) (hx_own x)
  (hx_regs x) (hx_RLO x) (hx_RHI x) akey aph apad asens gotw guard dcs
  (hx_null x) (hx_P x) (hx_O x) (hx_R x) (hx_cap x) (hx_ev x) (hx_bs x).
End l.

(* ======================================= the facts every cut carries ======================================= *)
(* the thirteen saved words and fs0's entry bits in the frame *)
Definition hp_saved_ok (x : hp_ctx) (mem : word -> option byte) : Prop :=
Forall (fun c => val_mem segs (hx_rd x mem) (hx_sp x + fst c) 8 (bv_unsigned (getr (hx_regs x) (Z_to_bv 5 (snd c)))))
  HP_SAVED /\
val_mem segs (hx_rd x mem) (hx_sp x + HP_FS0) 8 (bv_unsigned (Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8))).

(* a byte of the hole: one of the eight shadow bytes of the frame object *)
Definition hp_hole (x : hp_ctx) (a : Z) : Prop := hx_shf x <= a < hx_shf x + 8.

(* the parse's writes for its caller once n cells are written: out[0, 3 n), res when res <> 0, the errno cell *)
Definition hp_pw (x : hp_ctx) (n a : Z) : Prop :=
(hx_O x <= a < hx_O x + 3 * n) \/ (hx_R x <> 0 /\ hx_R x <= a < hx_R x + 12) \/
(as_errno B <= a < as_errno B + 4).

(* the float state at a cut: every float register but fs0, fa4 and fa5 as at the entry, rounding mode 0; inside
   the pair loop also fs0 = +0.0 (`fmv.d.x fs0,zero` in the loop's setup) *)
(* (the float state at a cut is given by its registers F and its status word fc, so that no second float state is a
   local instance where the entry state fx is resolved) *)
Definition hp_fx (F : bvmap 5 word) (fc : bv 32) : Prop := hd_fxk [8; 14; 15] fx (mkFP F fc).
Definition hp_fxw (F : bvmap 5 word) (fc : bv 32) : Prop :=
hp_fx F fc /\ Sem.reg_get F (Z_to_bv 5 8) = Z_to_bv 64 0.

(* The core of a cut inside the hole with the pattern pat, the cells cl written to out and res's twelve bytes rb
   (res is zeroed at the entry and written at the walk's end): the caller's journal over the unpoisoned memory, the
   caller's I/O state, every byte outside the parse's stack window, the hole and the parse's writes as at the call,
   the saved words, out[0, 3 |cl|) = the cells, res = rb when res <> 0, the errno cell readable, and sp = spa,
   s0 = sp0, gp, tp as at the call, s1 = res, s2 = cap, s3 = out, s10 = the hole's first byte, s11 = the shadow
   offset. *)
Definition hp_core (x : hp_ctx) (pat : list Z) (cl : list Headamp.cell) (rb : list byte)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
hjournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) mem2 md2 (hx_k x) (hx_fr x) pat /\
same_io (hx_mdc x) md2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a ->
 ~ hp_pw x (Z.of_nat (length cl)) a ->
 hx_view x mem2 a = hx_view x (hx_memc x) a) /\
hp_saved_ok x mem2 /\
garr8 segs (hx_rd x mem2) (hx_O x) (hd_zbytes (ha_cells_bytes cl)) /\
(hx_R x <> 0 -> garr8 segs (hx_rd x mem2) (hx_R x) (hd_zbytes rb)) /\
(exists ev', rd32 (hx_view x mem2) (as_errno B) ev') /\
getr regs2 2 = w64 (hx_spa x) /\ getr regs2 8 = w64 (hx_sp x) /\
getr regs2 3 = getr (hx_regs x) 3 /\ getr regs2 4 = getr (hx_regs x) 4 /\
getr regs2 9 = w64 (hx_R x) /\ getr regs2 18 = w64 (hx_cap x) /\ getr regs2 19 = w64 (hx_O x) /\
getr regs2 26 = w64 (hx_shf x) /\ getr regs2 27 = w64 SHADOW_OFF.

(* ======================================= the model facts per cut ======================================= *)
(* the params Struct pod at r + 8 (its value of the property at r): body r + 16, vs = its size *)
Definition hp_vs (x : hp_ctx) (r : Z) : Z := Spa.u32_at (hx_bs x) (r + 8).
Definition hp_st_ok (x : hp_ctx) (r : Z) : Prop :=
16 <= r /\ r mod 8 = 0 /\ hp_vs x r < Spa.SPA_POD_MAX_SIZE /\ r + 16 + hp_vs x r <= hx_len x.
(* the child at cc lies inside the Struct body (spa_pod_is_inside passed) and the next child's offset *)
Definition hp_child_in (x : hp_ctx) (r cc : Z) : Prop := Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = true.
Definition hp_next (x : hp_ctx) (cc : Z) : Z := cc + Spa.round_up8 (8 + Spa.u32_at (hx_bs x) cc).
(* a pending key: the String child at ck lies in the pod and is a key (spa_pod_get_string), its text hp_kstr *)
Definition hp_key_ok (x : hp_ctx) (ck : Z) : Prop :=
0 <= ck /\ ck + 8 + Spa.u32_at (hx_bs x) ck <= hx_len x /\ Spa.spa_get_string (Spa.child_at (hx_bs x) ck) <> None.
Definition hp_kstr (x : hp_ctx) (ck : Z) : list byte :=
match Spa.spa_get_string (Spa.child_at (hx_bs x) ck) with Some k => k | None => [] end.
Definition hp_l2key (x : hp_ctx) (ko : option Z) : option (list byte) :=
match ko with None => None | Some ck => Spa.spa_get_string (Spa.child_at (hx_bs x) ck) end.
(* the key register: 0, or the key text's address P + ck + 8 *)
Definition hp_keyv (x : hp_ctx) (ko : option Z) : Z := match ko with None => 0 | Some ck => hx_P x + ck + 8 end.
(* the fold's state: cells within cap, keys counted, the refusal one of the six codes *)
Definition hp_st (x : hp_ctx) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
Z.of_nat (length cl) <= hx_cap x /\ 0 <= keys /\ 0 <= rf <= 5.

(* the find loop at the property offset r with fuel n (more than the bytes left) *)
Definition hp_m_find (x : hp_ctx) (r : Z) (n : nat) : Prop :=
hx_null x = 0 /\ Spa.is_object_type (hx_bs x) Model.POD_OBJECT_PROPS = true /\ 16 <= hx_SZ x /\
16 <= r <= hx_len x + 7 /\ r mod 8 = 0 /\ (Z.to_nat (8 + hx_SZ x - r) < n)%nat /\
hx_res x = match Spa.find_prop (hx_bs x) (hx_SZ x) Model.POD_PROP_PARAMS r n with
           | None => (0, [], (0, 0, Headamp.REFUSE_NONE))
           | Some r' =>
               if Spa.is_struct_at (hx_bs x) (r' + 8)
               then Headamp.ha_result (Headamp.ha_fold Headamp.parse_cell (hx_cap x)
                      (hp_walk_pairs (hx_bs x) r' (r' + 16) (length (hx_bs x)) None) [] 0 Headamp.REFUSE_NONE)
               else (0, [], (0, 0, Headamp.REFUSE_NONE))
           end.

(* the pair loop's head at the child cc with fuel n (more than the bytes left), the key slot ko, the state *)
Definition hp_m_walk (x : hp_ctx) (r cc : Z) (n : nat) (ko : option Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
hx_null x = 0 /\ hp_st_ok x r /\ r + 16 <= cc <= r + 16 + hp_vs x r + 7 /\ cc mod 8 = 0 /\
(Z.to_nat (r + 16 + hp_vs x r - cc) < n)%nat /\ (forall ck, ko = Some ck -> hp_key_ok x ck) /\ hp_st x cl keys rf /\
hx_res x = Headamp.ha_result (Headamp.ha_fold Headamp.parse_cell (hx_cap x)
             (hp_walk_pairs (hx_bs x) r cc n (hp_l2key x ko)) cl keys rf).

(* the advance from the child cc (inside the body) to the next child, with fuel n there and the key slot ko *)
Definition hp_m_adv (x : hp_ctx) (r cc : Z) (n : nat) (ko : option Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
hx_null x = 0 /\ hp_st_ok x r /\ r + 16 <= cc /\ cc mod 8 = 0 /\ hp_child_in x r cc /\
(Z.to_nat (r + 16 + hp_vs x r - cc) < S n)%nat /\ (forall ck, ko = Some ck -> hp_key_ok x ck) /\ hp_st x cl keys rf /\
hx_res x = Headamp.ha_result (Headamp.ha_fold Headamp.parse_cell (hx_cap x)
             (hp_walk_pairs (hx_bs x) r (hp_next x cc) n (hp_l2key x ko)) cl keys rf).

(* the key at ck has the prefix (strncmp returned 0) and its value is the child cc *)
Definition hp_m_key (x : hp_ctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
hx_null x = 0 /\ hp_st_ok x r /\ r + 16 <= cc /\ cc mod 8 = 0 /\ hp_child_in x r cc /\
(Z.to_nat (r + 16 + hp_vs x r - cc) < S n)%nat /\ hp_key_ok x ck /\ hp_st x cl keys rf /\
Headamp.ha_prefix (hp_kstr x ck) = true /\
hx_res x = Headamp.ha_result (hp_fold_after (hx_cap x) (Headamp.parse_cell (hp_kstr x ck) (Spa.child_at (hx_bs x) cc))
             (hp_walk_pairs (hx_bs x) r (hp_next x cc) n None) cl keys rf).

(* the key read as the cell address (ch, p); its value is the child cc *)
Definition hp_m_val (x : hp_ctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
hx_null x = 0 /\ hp_st_ok x r /\ r + 16 <= cc /\ cc mod 8 = 0 /\ hp_child_in x r cc /\
(Z.to_nat (r + 16 + hp_vs x r - cc) < S n)%nat /\ hp_st x cl keys rf /\
0 <= ch < Headamp.REAC_HEADAMP_MAX_CH /\ 0 <= p <= Headamp.HA_SENS /\
hx_res x = Headamp.ha_result (hp_fold_after (hx_cap x) (hp_vcell ch p (Spa.child_at (hx_bs x) cc))
             (hp_walk_pairs (hx_bs x) r (hp_next x cc) n None) cl keys rf).

(* the walk's end with the folded state (cl, keys, rf) *)
Definition hp_m_exit (x : hp_ctx) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
hx_null x = 0 /\ hp_st x cl keys rf /\ hx_res x = Headamp.ha_result (cl, keys, rf).

End b.
