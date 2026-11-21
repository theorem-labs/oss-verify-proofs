(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the walk of musl's __vdsosym at LPS 727298f3 (auxv pair 0, the vDSO ELF header, program headers, dynamic section, hash table, symbol and version tables) to its clock_gettime entry. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/Ref/RVdsoWalk.v, with its module paths, module names and numbers changed; 286 of its 414 lines of code are new or changed and 13 lines of the source are left out; taken from projects/openssl/echconfiglist_parser/proofs/lib/Ref/RVdsoWalk.v, lines 26-31, 33-42, 55-155, 159-160, 167-182, 184-191 and 193-202, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the walk of musl's __vdsosym in the ASan build
   (echconfiglist_parser.asan), the As copy of Ref/RVdsoWalk.v.

   WHAT IS WALKED.  musl 1.2's [__vdsosym(vername, name)] (src/internal/vdso.c), from its entry
   to its return, over the run's segment list [asegs ++ tail]:
     - the auxv scan for AT_SYSINFO_EHDR (33), which is pair 0 at LPS 727298f3;
     - the ELF header and the program headers (PT_LOAD gives the load bias, PT_DYNAMIC the dynamic
       section);
     - the dynamic section (DT_STRTAB, DT_SYMTAB, DT_GNU_HASH, DT_VERSYM, DT_VERDEF; the image has
       no DT_HASH);
     - [count_syms] over the GNU hash table (a leaf at 0x535270);
     - the symbol loop and [checkver].
   Every byte of the vDSO is read through [Lib/VdsoImg.v]'s [rvdso_read], at the offset the
   instruction's address names, and every branch is decided by proof ([vif]).

   WHAT DIFFERS FROM THE REF WALK: the two string compares.  ASan intercepts strcmp, so
   [__vdsosym]'s calls (at 0x535208 in the symbol loop, at 0x53519c in checkver, AVdsoAddr.v)
   jump to the interceptor's slot 0x1ad7d8 instead of musl's strcmp.  The walk takes each such
   call whole, by [evt_cut] and the interceptor's contract [AsStrcmp.astrcmp_thunk_ok]: the
   string at a0 is the binary's "__vdso_clock_gettime" (or "LINUX_4.15" in checkver), the
   string at a1 a string of the vDSO's string table, its bytes computed from the image
   ([avw_cstrlen], [rvdso_byte_list]); the answer is 0 exactly when the two are equal, which is
   decided by computing both.  Measured from the image (Python reading of Vdso.v's bytes, checked
   by [avw_strtab_measured] and [avw_strsz_measured] below): the loop compares the name with the
   strings at string-table offsets 42, 62, 170, 116, 137, 1 and 21 (seven calls, the last equal),
   then checkver compares "LINUX_4.15" with offset 170 (equal).

   THE PREMISES are the Ref walk's (the auxv cell holds the auxv base [av], whose first pair is
   (33, vb); the image is mapped at [vb] in the run's list; the frame fits above [lo]), plus what
   the interceptor's contract asks at each call, stated once over the memory at the entry: the
   interceptor's cells ([astrcmp_cells]), the shadow of the binary's two strings and of the
   whole vDSO string table [vb + AVW_STRTAB, vb + AVW_STRTAB + AVW_STRSZ) ([astrcmp_shz]), the
   interceptor's stack ceiling ([aceil <= lo]) and the image below the stack ([vb + RVDSO_SPAN <=
   lo]).  The stack the walk uses is 0x70 + 2208 = 2320 bytes (AVdsoSym.AVW_FRAME). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Decode VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsStrcmp.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import AVdsoAddr AVdsoSegs AVdsoSym.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma av_land_ones64_l : forall w : word, Z.land 18446744073709551615 (bv_unsigned w) = bv_unsigned w.
Proof.
  intros w. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. exact R.
Qed.

Lemma av_land_ones64_r : forall w : word, Z.land (bv_unsigned w) 18446744073709551615 = bv_unsigned w.
Proof. intros w. rewrite Z.land_comm. apply av_land_ones64_l. Qed.

(* ------------------------------------------------------------------ *)
(* The vDSO's string table, read from the image.                       *)
(* ------------------------------------------------------------------ *)

(* DT_STRTAB = 0x270 and DT_STRSZ = 0xb5: the third and fifth entries of the dynamic section
   (PT_DYNAMIC at offset 0x378, 16-byte entries); the load bias is 0 (PT_LOAD at offset 0,
   vaddr 0). *)
Definition AVW_STRTAB : Z := 624.
Definition AVW_STRSZ : Z := 181.

Definition avw_bu (b : byte) : Z := bv_unsigned b.

Lemma avw_strtab_measured :
  map avw_bu (firstn 16%nat (skipn 920%nat rvdso_bytes)) = [5; 0; 0; 0; 0; 0; 0; 0; 112; 2; 0; 0; 0; 0; 0; 0].
Proof. vm_compute. reflexivity. Qed.

Lemma avw_strsz_measured :
  map avw_bu (firstn 16%nat (skipn 952%nat rvdso_bytes)) = [10; 0; 0; 0; 0; 0; 0; 0; 181; 0; 0; 0; 0; 0; 0; 0].
Proof. vm_compute. reflexivity. Qed.

(* The length of the NUL-terminated string at image offset [o] (at most 64). *)
Fixpoint avw_cstrlen_go (o : Z) (k : nat) : nat :=
  match k with
  | O => O
  | S k' => if Z.eqb (bv_unsigned (rvdso_byte o)) 0 then O else S (avw_cstrlen_go (o + 1) k')
  end.
Definition avw_cstrlen (o : Z) : nat := avw_cstrlen_go o 64%nat.

Lemma avw_eq_u : forall l1 l2 : list byte, map avw_bu l1 = map avw_bu l2 -> l1 = l2.
Proof.
  induction l1 as [|b l1 IH]; intros [|b2 l2] H; cbn [map] in H; try discriminate H; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | exact (IH l2 H2)].
Qed.

Lemma avw_nonul : forall s : list byte,
  forallb (fun b => negb (Z.eqb (bv_unsigned b) 0)) s = true -> ~ In (Z_to_bv 8 0) s.
Proof.
  induction s as [|b s IH]; intros H Hin; [exact Hin|].
  cbn [forallb] in H. apply andb_true_iff in H. destruct H as [H1 H2].
  destruct Hin as [E|Hin].
  - subst b. vm_compute in H1. discriminate H1.
  - exact (IH H2 Hin).
Qed.

(* ------------------------------------------------------------------ *)
(* The walk's tactics (Ref/RVdsoWalk.v's).                             *)
(* ------------------------------------------------------------------ *)

Local Ltac vclosedZ c :=
  lazymatch c with
  | Z0 => constr:(tt)
  | Zpos _ => constr:(tt)
  | Zneg _ => constr:(tt)
  | Z.add ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.sub ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.mul ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.opp ?a => vclosedZ a
  | Z.shiftl ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.shiftr ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.land ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.lor ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.lxor ?a ?b => let k := vclosedZ a in vclosedZ b
  | bv_unsigned (Z_to_bv _ ?a) => vclosedZ a
  | bv_signed (Z_to_bv _ ?a) => vclosedZ a
  | bv_wrap _ ?a => vclosedZ a
  | bv_unsigned (@BV _ ?a _) => vclosedZ a
  | _ => fail 1 "vclosedZ: not a closed Z expression"
  end.

Local Ltac vdso_off vb E :=
  lazymatch E with
  | context [vb] =>
      let f := eval pattern vb in E in
      lazymatch f with
      | ?g vb =>
          let t := eval cbv beta in (g 0) in
          let k := vclosedZ t in
          let o := eval vm_compute in t in
          zlit o
      end
  | _ => fail 1 "vdso_off: address does not mention the vDSO base"
  end.

Local Ltac vzred :=
  fold_closed_in_goal;
  repeat (match goal with
          | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
          end; fold_closed_in_goal).

Local Ltac vaddr_eq :=
  unfold wa; first [ reflexivity | f_equal; vzred; lia ].

Local Ltac solve_load_vdso :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    lazymatch goal with
    | ROM : rvdso_rom segs ?vb, MI : mem_inv segs m |- _ =>
        let E := addr_expr a in
        let o := vdso_off vb E in
        let bs := eval vm_compute in (firstn n (skipn (Z.to_nat o) rvdso_bytes)) in
        let RD := fresh "RDV" in
        assert (RD : ov_read_bytes segs m (wa (vb + o)) n = Some bs)
          by (apply (rvdso_read segs m vb o n bs (rvdso_ok_of_rom segs m vb ROM MI));
              [ lia | rewrite RVDSO_SIZE_val; lia | vm_compute; reflexivity ]);
        replace (ov_read_bytes segs m a n) with (Some bs)
          by (rewrite <- RD; f_equal; vaddr_eq);
        clear RD; load_post
    end
  end.

Local Ltac solve_load ::= first [ solve_load_base | solve_load_image | solve_load_vdso ].

Local Ltac vcond := unfold_cond; fold_lit_ux; vzred; solve_cond_rec.
Local Ltac vif :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by (symmetry; vcond); cbv iota
            | replace c with false by (symmetry; vcond); cbv iota ]
  end.

Local Ltac vbool_once :=
  first
  [ match goal with |- context [v_sltiu _ _] => unfold v_sltiu end
  | match goal with |- context [v_sltu _ _] => unfold v_sltu, c_ltu end
  | match goal with
    | |- context [Z.ltb ?a ?b] =>
        first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; vzred; lia)
              | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; vzred; lia) ]
    end
  | match goal with
    | |- context [Z.eqb ?a ?b] =>
        first [ replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; vzred; lia)
              | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; vzred; lia) ]
    end
  | progress (cbv beta iota)
  | progress fold_closed_in_goal
  | progress (rewrite ?av_land_ones64_l, ?av_land_ones64_r)
  | progress (rewrite ?Z_to_bv_lit_self) ].
Local Ltac vbool := progress (repeat vbool_once).

Section Walk.
  Context {HCEIL : HeapCeil}.
  Variable tail : list Segment.

  Local Notation VS := (VW_BSEGS ++ tail).

  (* ---------------- the strings the interceptor compares ---------------- *)

  (* [n] bytes of the vDSO image from offset [o], read at [vb + o] *)
  Lemma av_rvdso_bytes_at : forall (m : word -> option byte) vb o n,
    rvdso_rom VS vb -> mem_inv VS m -> 0 <= o -> o + Z.of_nat n <= RVDSO_SIZE ->
    bytes_at VS m (vb + o) (rvdso_byte_list o n).
  Proof.
    intros m vb o n (V0 & VA & VH & ROM) MI Ho Hn.
    pose proof RVDSO_SIZE_span as [S0 S1].
    split; [lia|]. split; [rewrite length_rvdso_byte_list; lia|].
    intros i Hi. rewrite length_rvdso_byte_list in Hi.
    rewrite nth_error_rvdso_byte_list by exact Hi.
    assert (Ho' : 0 <= o + Z.of_nat i < RVDSO_SIZE) by lia.
    destruct (ROM (o + Z.of_nat i) Ho') as [RB RO].
    replace (vb + o + Z.of_nat i) with (vb + (o + Z.of_nat i)) by lia.
    unfold mrd. destruct (m (wa (vb + (o + Z.of_nat i)))) as [b|] eqn:EM.
    - exfalso. rewrite (MI _ _ EM) in RO. discriminate RO.
    - rewrite RB, (rvdso_peek_in _ Ho'). reflexivity.
  Qed.

  (* a NUL-terminated string of the image, in the form the interceptor's contract asks *)
  Lemma av_vstr_bytes : forall (m : word -> option byte) vb o n (s : list byte),
    rvdso_rom VS vb -> mem_inv VS m -> 0 <= o -> o + Z.of_nat n + 1 <= RVDSO_SIZE ->
    map avw_bu (s ++ [Z_to_bv 8 0]) = map avw_bu (rvdso_byte_list o (S n)) ->
    bytes_at VS m (vb + o) (s ++ [Z_to_bv 8 0]).
  Proof.
    intros m vb o n s ROM MI Ho Hn E.
    rewrite (avw_eq_u _ _ E).
    apply av_rvdso_bytes_at; [exact ROM | exact MI | exact Ho | lia].
  Qed.

  (* the binary's two strings, read-only data of its first segment *)
  Lemma av_name_bytes : forall (m : word -> option byte), mem_inv VS m ->
    bytes_at VS m VW_NAME (VW_NAME_S ++ [Z_to_bv 8 0]).
  Proof.
    intros m MI.
    assert (RO : ro_cells VS m VW_NAME [CB (length (VW_NAME_S ++ [Z_to_bv 8 0])) (VW_NAME_S ++ [Z_to_bv 8 0])]).
    { apply ro_cells_image;
        [ exact MI | vm_compute; reflexivity
        | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity ]. }
    destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  Qed.

  Lemma av_vername_bytes : forall (m : word -> option byte), mem_inv VS m ->
    bytes_at VS m VW_VERNAME (VW_VERNAME_S ++ [Z_to_bv 8 0]).
  Proof.
    intros m MI.
    assert (RO : ro_cells VS m VW_VERNAME
                   [CB (length (VW_VERNAME_S ++ [Z_to_bv 8 0])) (VW_VERNAME_S ++ [Z_to_bv 8 0])]).
    { apply ro_cells_image;
        [ exact MI | vm_compute; reflexivity
        | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity ]. }
    destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  Qed.

  (* ---------------- the contract's premises across the walk's own writes ---------------- *)

  (* As/AsStrcmp.v's [asc_shz_frame]: shadow bytes lie below AHI_LO, the frame above it. *)
  Lemma av_shz_frame : forall (m m' : word -> option byte) x n lo' hi',
    astrcmp_shz tail m x n -> munch [(lo', hi')] m m' -> AHI_LO <= lo' -> astrcmp_shz tail m' x n.
  Proof.
    intros m m' x n lo' hi' (H0 & Hn & H1 & H) MU Hlo.
    split; [exact H0|]. split; [exact Hn|]. split; [exact H1|].
    intros a Ha. unfold AHI_LO in Hlo. unfold AAPP_HI in H1. pose proof ASHADOW_BASE_val as HSB.
    pose proof (asc_sh_range x ltac:(lia)) as R0.
    pose proof (asc_sh_range (x + n) ltac:(lia)) as R1.
    assert (D0 : 0 <= sh x / 8) by (apply Z.div_pos; lia).
    pose proof (Z.div_mod (sh (x + n)) 8 ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (sh (x + n)) 8 ltac:(lia)) as MB.
    assert (A1 : a < AHI_LO) by (unfold AHI_LO; lia). unfold AHI_LO in A1.
    assert (OUT : outside [(lo', hi')] (bv_unsigned (wa a))).
    { rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
    unfold mrd. rewrite (MU (wa a) OUT). exact (H a Ha).
  Qed.

  (* a sub-range of a range whose shadow reads 0, after the walk's writes above AHI_LO *)
  Lemma av_shz_at : forall (m0 m : word -> option byte) X N x n lo' hi',
    astrcmp_shz tail m0 X N -> munch [(lo', hi')] m0 m -> AHI_LO <= lo' ->
    X <= x -> 0 <= n -> x + n <= X + N -> astrcmp_shz tail m x n.
  Proof.
    intros m0 m X N x n lo' hi' SZ MU Hlo Hx Hn Hxn.
    apply (av_shz_frame m0 m x n lo' hi'); [| exact MU | exact Hlo].
    destruct SZ as (H0 & HN & H1 & H).
    split; [lia|]. split; [exact Hn|]. split; [lia|].
    intros a Ha. apply H.
    pose proof (sh_mono X x Hx) as M1.
    pose proof (sh_mono (x + n) (X + N) Hxn) as M2.
    assert (D1 : sh X / 8 <= sh x / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : sh (x + n) / 8 <= sh (X + N) / 8) by (apply Z.div_le_mono; lia).
    lia.
  Qed.

  (* the interceptor's cells all lie in the image, below AIMG_TOP *)
  Lemma av_cells_frame : forall (m m' : word -> option byte) lo' hi',
    astrcmp_cells tail m -> munch [(lo', hi')] m m' -> AIMG_TOP <= lo' -> astrcmp_cells tail m'.
  Proof.
    intros m m' lo' hi' (C1 & C2 & C3 & C4 & C5 & C6) MU Hlo.
    assert (OUT : forall a, 0 <= a < AIMG_TOP -> mrd VS m' (wa a) = mrd VS m (wa a)).
    { intros a Ha. unfold mrd. rewrite (MU (wa a)); [reflexivity|].
      unfold AIMG_TOP in *. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
    unfold astrcmp_cells. unfold AIMG_TOP in Hlo.
    split; [| split; [| split; [| split; [| split]]]].
    - eapply ro_cells_transport; [exact C1 | exact MU |].
      unfold ASTRCMP_GOT_CFLAGS. cbn [disjoint_from cells_size csize Nat.add]. lia.
    - eapply ro_cells_transport; [exact C2 | exact MU |].
      unfold ASTRCMP_GOT_SHBASE. cbn [disjoint_from cells_size csize Nat.add]. lia.
    - eapply ro_cells_transport; [exact C3 | exact MU |].
      unfold ASTRCMP_SHBASE_CELL. cbn [disjoint_from cells_size csize Nat.add]. lia.
    - rewrite OUT by (unfold ASTRCMP_INITED, AIMG_TOP; lia). exact C4.
    - rewrite OUT by (unfold ASTRCMP_ISTRCMP_CELL, AIMG_TOP; lia). exact C5.
    - rewrite OUT by (unfold ASTRCMP_STRICT_CELL, AIMG_TOP; lia). exact C6.
  Qed.

  (* ---------------- the calls to the interceptor ---------------- *)

  (* the bytes of an operand: the binary's name or version string, or a string of the image *)
  Local Ltac vstr_bytes :=
    lazymatch goal with
    | MIx : mem_inv _ ?mm |- bytes_at _ ?mm (bv_unsigned ?a) _ =>
        let E := addr_expr a in
        first
        [ let Ez := zlit E in
          lazymatch (eval vm_compute in (Z.eqb Ez VW_NAME)) with
          | true => rewrite (unsigned_lit Ez) by lia; exact (av_name_bytes mm MIx)
          end
        | let Ez := zlit E in
          lazymatch (eval vm_compute in (Z.eqb Ez VW_VERNAME)) with
          | true => rewrite (unsigned_lit Ez) by lia; exact (av_vername_bytes mm MIx)
          end
        | lazymatch goal with
          | ROMx : rvdso_rom _ ?vb |- _ =>
              let o := vdso_off vb E in
              let n := eval vm_compute in (avw_cstrlen o) in
              let s := eval vm_compute in (rvdso_byte_list o n) in
              let EA := fresh "EA" in
              assert (EA : bv_unsigned a = vb + o) by (vzred; lia);
              rewrite EA; clear EA;
              apply (av_vstr_bytes mm vb o n s ROMx MIx);
              [ lia | rewrite RVDSO_SIZE_val; lia | vm_compute; reflexivity ]
          end ]
    end.

  (* the shadow premise of an operand, from the entry's ([SZN], [SZV], [SZT]) and [MU]; the
     hypotheses are arguments, since an Ltac definition cannot name the proof's hypotheses *)
  Local Ltac vstr_shz SZN SZV SZT MU :=
    lazymatch goal with
    | |- astrcmp_shz _ ?mm (bv_unsigned ?a) (Z.of_nat (length ?s)) =>
        let n := eval vm_compute in (Z.of_nat (length s)) in
        change (Z.of_nat (length s)) with n;
        let E := addr_expr a in
        first
        [ let Ez := zlit E in
          rewrite (unsigned_lit Ez) by lia;
          first
          [ eapply av_shz_at;
              [ exact SZN | exact MU | unfold AHI_LO; lia | unfold VW_NAME; lia | lia | unfold VW_NAME; lia ]
          | eapply av_shz_at;
              [ exact SZV | exact MU | unfold AHI_LO; lia | unfold VW_VERNAME; lia | lia | unfold VW_VERNAME; lia ] ]
        | lazymatch goal with
          | ROMx : rvdso_rom _ ?vb |- _ =>
              let o := vdso_off vb E in
              let EA := fresh "EA" in
              assert (EA : bv_unsigned a = vb + o) by (vzred; lia);
              rewrite EA; clear EA;
              eapply av_shz_at;
                [ exact SZT | exact MU | unfold AHI_LO; lia | unfold AVW_STRTAB; lia | lia
                | unfold AVW_STRTAB, AVW_STRSZ; lia ]
          end ]
    end.

  (* an operand off the interceptor's frame *)
  Local Ltac vstr_sep :=
    unfold ASTRCMP_FRAME;
    repeat match goal with
           | |- context [length ?s] => let n := eval vm_compute in (length s) in change (length s) with n
           end;
    vzred;
    first [ left; lia | right; lia ].

  Local Ltac vcall_side SZN SZV SZT MU CELLS :=
    lazymatch goal with
    | |- bytes_at _ _ _ _ => vstr_bytes
    | |- ~ In _ _ => apply avw_nonul; vm_compute; reflexivity
    | |- (_ < 64)%nat \/ _ => left; apply Nat.ltb_lt; vm_compute; reflexivity
    | |- astrcmp_shz _ _ _ _ => vstr_shz SZN SZV SZT MU
    | |- astrcmp_cells _ _ => eapply av_cells_frame; [exact CELLS | exact MU | unfold AIMG_TOP; lia]
    | |- _ \/ _ => vstr_sep
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; assumption
    | |- mem_inv _ _ => assumption
    | |- _ <= _ => first [ assumption | unfold ASTRCMP_FRAME; rewrite ?unsigned_lit by lia; lia ]
    end.

  (* the caller's facts across the call: its frame, the auxv cells, the footprint *)
  Local Ltac vtransport mo mN MUc WMc :=
    let W := lazymatch type of MUc with munch ?W _ _ => W end in
    repeat match goal with
    | H : rw_cells (asegs ++ tail) mo ?A2 ?cs2 |- _ =>
        apply (rw_cells_transport (asegs ++ tail) W mo mN A2 cs2) in H;
        [ | exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia ]
    | H : ro_cells (asegs ++ tail) mo ?A2 ?cs2 |- _ =>
        apply (ro_cells_transport (asegs ++ tail) W mo mN A2 cs2) in H;
        [ | exact MUc | cbn [disjoint_from cells_size csize Nat.add]; lia ]
    | H : munch ?Wq ?mq mo |- _ =>
        apply (munch_trans Wq mq mo mN) in H;
        [ | apply (munch_weaken W Wq mo mN);
            [ unfold sub_fp; intros xq Hxq; cbn [outside] in Hxq |- *; repeat split; lia
            | exact MUc ] ]
    | H : wmono (asegs ++ tail) ?mq mo |- _ =>
        apply (wmono_trans (asegs ++ tail) mq mo mN) in H; [ | exact WMc ]
    end.

  (* after the call: the post, the caller's facts moved over, the answer decided; [ST] and [MI]
     are the walk's stack and memory-invariant hypotheses, renamed onto the post's *)
  Local Ltac vcall_post ST MI :=
    let msx := fresh "ms" in let PO := fresh "PO" in
    intros msx PO;
    let r := fresh "r" in destruct PO as [r PO];
    let y1 := fresh "y" in destruct PO as [y1 PO];
    let y2 := fresh "y" in destruct PO as [y2 PO];
    let y3 := fresh "y" in destruct PO as [y3 PO];
    let y4 := fresh "y" in destruct PO as [y4 PO];
    let mN := fresh "m" in destruct PO as [mN PO];
    let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in
    let STc := fresh "STc" in let RES := fresh "RES" in
    destruct PO as (-> & MUc & WMc & MIc & STc & RES);
    unfold ASTRCMP_FRAME in MUc;
    rewrite unsigned_lit in MUc, STc by lia;
    lazymatch type of MUc with
    | munch _ ?mo _ =>
        vtransport mo mN MUc WMc;
        clear MUc WMc;
        try clear ST; rename STc into ST;
        repeat match goal with H : mem_inv _ mo |- _ => clear H end;
        rename MIc into MI;
        try clear mo
    end;
    first
    [ let RZ := fresh "RZ" in
      assert (RZ : r = Z_to_bv 64 0) by (apply (proj2 RES); apply avw_eq_u; vm_compute; reflexivity);
      subst r; clear RES
    | let RNZ := fresh "RNZ" in
      assert (RNZ : bv_unsigned r <> 0)
        by (let HZ := fresh "HZ" in let E := fresh "E" in
            intros HZ;
            assert (E : r = Z_to_bv 64 0) by (apply bv_eq; rewrite HZ; reflexivity);
            apply (proj1 RES) in E; apply (f_equal (map avw_bu)) in E;
            vm_compute in E; discriminate E);
      clear RES ];
    lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k)
          by (symmetry; apply ret_pc_even; [lia | reflexivity])
    end.

  (* a call at the interceptor's slot, taken whole by its contract [SC] *)
  Local Ltac vcall_strcmp SC LO SZN SZV SZT MU CELLS ST MI :=
    eapply evt_cut;
    [ eapply SC with (lo := LO); vcall_side SZN SZV SZT MU CELLS
    | vcall_post ST MI ].

  Local Ltac vone SC LO SZN SZV SZT MU CELLS ST MI :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        lazymatch (eval vm_compute in (Z.eqb pc VW_STRCMP_SLOT)) with
        | true => first [ vcall_strcmp SC LO SZN SZV SZT MU CELLS ST MI | fail 100 "AVdsoWalk: the strcmp call at" pc "did not close" ]
        | false => first [ step | vif | vbool ]
        end
    | _ => first [ step | vif | vbool ]
    end.

  (* [a0] and [a1] are the two strings cgt_init passes: "LINUX_4.15" and "__vdso_clock_gettime"
     in the binary's read-only data ([AVdsoAddr.v]). *)
  Lemma avdsosym_walk :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
           (a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo av vb : Z),
      ro_cells VS m VW_AUXV_CELL [C8 (Z_to_bv 64 av)] ->
      ro_cells VS m av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 vb)] ->
      rvdso_rom VS vb -> 0 < vb ->
      mem_inv VS m -> stk VS m lo (bv_unsigned sp) ->
      VW_AUXV_CELL + 8 <= lo -> lo + 2320 <= bv_unsigned sp -> bv_unsigned sp <= av ->
      aceil <= lo -> vb + RVDSO_SPAN <= lo ->
      astrcmp_cells tail m ->
      astrcmp_shz tail m VW_NAME 20 -> astrcmp_shz tail m VW_VERNAME 10 ->
      astrcmp_shz tail m (vb + AVW_STRTAB) (AVW_STRSZ - 1) ->
      evt VS
        (avdsosym_post_v tail vb ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 VW_VERNAME) (Z_to_bv 64 VW_NAME)
                 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VW_ENTRY) fc None m (seg_rom VS)).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m lo av vb
           CELL AUX ROM VBP MI ST CLO LOB SPA CEIL VBLO CELLS SZN SZV SZT.
    acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof ROM as (VB0 & VBA & VBH & _). rewrite RVDSO_SPAN_val in VBH.
    pose proof VBLO as VBL8. rewrite RVDSO_SPAN_val in VBL8.
    unfold VW_AUXV_CELL in CELL, CLO.
    pose proof (astrcmp_thunk_ok tail) as SC. unfold astrcmp_contract_at, ASTRCMP_THUNK in SC.
    pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl (asegs ++ tail) m) as WM.
    unfold VW_ENTRY, VW_VERNAME, VW_NAME.
    (* addi sp, sp, -0x70, then the frame *)
    step. carve_frame 112%nat ST.
    repeat (vone SC lo SZN SZV SZT MU CELLS ST MI).
    lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc ra) _ _ _ _) => idtac
    | _ => step
    end.
    release_frame FR ST (bv_unsigned sp).
    finish.
    all: unfold RVDSO_CGT_OFF; vaddr_eq.
  Qed.

End Walk.
