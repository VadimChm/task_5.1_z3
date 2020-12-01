#include<iostream>
#include<z3++.h>
#include <vector>
using namespace z3;

enum comp_type
{
	L,
	G,
	LE,
	GE
};

struct swap_struct
{
	int i_elem;
	int j_elem;
	int swap;
};

class z3_sort_checker
{
	context c;
	solver s;

	int N;
	expr_vector elems_vec;
	expr_vector swaps_vec;
	std::vector<swap_struct> elems_swaps_base;

public:
	z3_sort_checker (int n) :
	c (),
	s (c),
	elems_vec (c),
	swaps_vec (c)
	{
		N = n;
		elems_swaps_base.clear ();
		for (int i = 0; i < N; i++)
    	{
    		std::stringstream x_name;
    		x_name << "x_" << i;
    		elems_vec.push_back (c.real_const(x_name.str().c_str()));
    	}
    	elems_swaps_base.push_back ({0, 0, 0});
    	swaps_vec.push_back (c.bool_const("s_0"));
	}	

	~z3_sort_checker ()
	{
	}

	void run ()
	{
		try 
		{
	        check_sort (); std::cout << "\n";
	    }

	    catch (exception & ex) 
	    {
	        std::cout << "unexpected error: " << ex << "\n";
	    }
	    Z3_finalize_memory();
	}


private:
	expr check_compare (int I, int J, comp_type comp)
	{
		expr comp_ok = elems_vec[elems_swaps_base[0].i_elem] > elems_vec[elems_swaps_base[0].i_elem];

		expr swaps_ok = elems_vec[elems_swaps_base[0].i_elem] == elems_vec[elems_swaps_base[0].i_elem];

		std::function<void (expr, int, int, int)> build_comp_ok;
		build_comp_ok = [&] (expr swap_way, int depth, int i_elem_ind, int j_elem_ind) {
			if (depth < elems_swaps_base.size ())
			{
				build_comp_ok (swap_way && !swaps_vec[elems_swaps_base[depth].swap], depth + 1, i_elem_ind, j_elem_ind);

				if (i_elem_ind == elems_swaps_base[depth].i_elem) i_elem_ind = elems_swaps_base[depth].j_elem;
				else if (i_elem_ind == elems_swaps_base[depth].j_elem) i_elem_ind = elems_swaps_base[depth].i_elem;
				if (j_elem_ind == elems_swaps_base[depth].i_elem) j_elem_ind = elems_swaps_base[depth].j_elem;
				else if (j_elem_ind == elems_swaps_base[depth].j_elem) j_elem_ind = elems_swaps_base[depth].i_elem;
				build_comp_ok (swap_way && swaps_vec[elems_swaps_base[depth].swap], depth + 1, i_elem_ind, j_elem_ind);
			}
			else 
			{
				switch (comp)
				{
					case L  : comp_ok = comp_ok || (elems_vec[i_elem_ind] <  elems_vec[j_elem_ind] && swap_way); break;
					case G  : comp_ok = comp_ok || (elems_vec[i_elem_ind] >  elems_vec[j_elem_ind] && swap_way); break;
					case LE : comp_ok = comp_ok || (elems_vec[i_elem_ind] <= elems_vec[j_elem_ind] && swap_way); break;
					case GE : comp_ok = comp_ok || (elems_vec[i_elem_ind] >= elems_vec[j_elem_ind] && swap_way); break;
					default: break;
				}
			}
		};

		build_comp_ok (swaps_ok, 0, I, J);
		return comp_ok;
	}

	void add_swap_conjuction (int I, int J, comp_type comp)
	{
		std::stringstream s_name;
		int swap_num = elems_swaps_base.size ();
    	s_name << "s_" << (swap_num - 1);
    	swaps_vec.push_back (c.bool_const(s_name.str().c_str()));

		s.add (check_compare (I, J, comp) && swaps_vec[swap_num]);
    	elems_swaps_base.push_back ({I, J, swap_num});
	}

	void check_sort ()
	{
		for (int i = 0; i < N; i++)
			for (int j = N - 1; j > i; j--)
			{
				add_swap_conjuction (j - 1, j, comp_type::G);
			}

	    expr check_bounds = check_compare (0, 1, comp_type::G);
	    for (int i = 2; i < N; i++)
	    	check_bounds = check_bounds || check_compare (i - 1, i, comp_type::G);

	    s.add (check_bounds);
	    if (s.check ())
	    {
	    	model m = s.get_model();
	    	std::cout << "Fail example:\n";

	    	for (int i = 0; i < m.size(); i++) 
	    	{
	        	func_decl v = m[i];
	        	assert(v.arity() == 0);
	         
	        	std::cout << v.name() << " = " << m.get_const_interp(v) << "\n";
	    	}
	    }
	    else 
	    {
	    	std::cout << "OK!\n";
	    }
	}

};

int main ()
{
	z3_sort_checker checker (6);
	checker.run ();
    return 0;
}