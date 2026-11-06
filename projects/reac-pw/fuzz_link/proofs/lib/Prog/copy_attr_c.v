(* copy_attr (reac_link_alias.c:25-35): the library`s cut of an attribute`s text into a buffer.

   a0 = a (a struct rtattr), a1 = out, a2 = n. A NULL out or a zero n is a no-op. Otherwise the
   payload is the a->rta_len - 4 bytes after the 4-byte header, the text is that payload up to its
   first NUL and to n-1 bytes, and a NUL is written after it. This is link_spec`s `cut_text`, the
   SAME function take_text computes on the harness side (fuzz_link.c:318-328), which is why the
   two sides` buffers hold the same C string. K = 80 (48 of its own plus strnlen`s 32; memcpy uses
   no stack). The separation premise is strnlen`s: the attribute is not inside this frame.
   THE POST REPEATS THE LENGTH BOUND (LinkLib's walker LbCopyAttr, 2026-10-30): `u16_at` fixes
   only l mod 2 ^ 16, so a Post quantified over a bare `forall l pay` lets l = 65540 with a
   65536-byte payload meet its premises, while `lhu a1, 0(a0)` at 0x163a4 reads 4 and the
   function writes only out[0] = 0 at 0x163d8. The Pre's existential carries the bound; the
   Post must carry it too, or it is false. The only caller, nl_talk, takes l from its own lhu.
   Entry read from the plain image (the unstripped twin of the pin ebe34b259b9f); the stack bound
   K is the function's own frame plus the deepest frame of every callee it can reach on the path
   this contract covers (link/ct/stack.py over both images). 
   THE BUFFER STAYS READABLE (LinkLib's L6, 2026-10-30): the Post must say the whole buffer is
   still `rw_cells`, not only the C string in front of it. `wmono` gives writability and not
   readability (`mrd` of a writable byte may be None), and the write set names the whole buffer, so
   a caller that uses it again has nothing to stand on: nl_talk calls copy_attr on the SAME buffer
   for a second IFLA_IFALIAS (0x161c4) or IFLA_INFO_KIND (0x161fc), and op_read hands the buffer to
   check_bounds, whose Pre is `tbuf_at`. It is provable: memcpy's Post covers the bytes it wrote,
   the rest of the buffer is untouched, and then one NUL store.
   *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
Local Open Scope Z_scope.

Definition COPY_ATTR : Z := 0x1637c.
Lemma COPY_ATTR_is_entry : COPY_ATTR = P_copy_attr. Proof. reflexivity. Qed.

Definition copy_attr_contract : Prop :=
  leaf COPY_ATTR 80
    (fun regs m => exists l pay,
       u16_at m (arg regs 0) l /\ RTA_HDR <= l <= 65535
       /\ bytes_at rsegs m (arg regs 0 + RTA_HDR) pay
       /\ Z.of_nat (length pay) = l - RTA_HDR
       /\ 0 < arg regs 0
       /\ arg regs 0 + RTA_HDR < 2 ^ 64
       /\ (arg regs 0 + l <= spZ regs - 80 \/ spZ regs <= arg regs 0)
       /\ (arg regs 1 <> 0 -> 1 <= arg regs 2 ->
             apart_frame regs 80 (arg regs 1) (arg regs 2)
             /\ (arg regs 1 + arg regs 2 <= arg regs 0 + RTA_HDR
                 \/ arg regs 0 + l <= arg regs 1)
             /\ exists junk, rw_cells rsegs m (arg regs 1) [CB (Z.to_nat (arg regs 2)) junk]))
    (fun regs m => [(arg regs 1, arg regs 1 + arg regs 2)])
    (fun regs m regs' m' =>
       (arg regs 1 = 0 -> m' = m)
       /\ (arg regs 2 = 0 -> munch [(spZ regs - 80, spZ regs)] m m')
       /\ (arg regs 1 <> 0 -> 1 <= arg regs 2 ->
             forall l pay, u16_at m (arg regs 0) l -> RTA_HDR <= l <= 65535 ->
               bytes_at rsegs m (arg regs 0 + RTA_HDR) pay ->
               Z.of_nat (length pay) = l - RTA_HDR ->
               cstr_at m' (arg regs 1) (cut_text pay (arg regs 2)))
       /\ (arg regs 1 <> 0 -> 1 <= arg regs 2 ->
             exists junk, rw_cells rsegs m' (arg regs 1) [CB (Z.to_nat (arg regs 2)) junk])
    ).
